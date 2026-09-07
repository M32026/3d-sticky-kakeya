module

/-
  ConcentratedHPrimeS.lean

  Adapted H' fiber lower bound for mass-half of direction-separated S.

  Main result: concentrated_H'_fiber_lower_mass_S
  - Takes S direction-separated at r/(4R_high), T_conc ⊆ S with mass-half of S
  - Uses generalized overlap bound ≤ F = floor(16π·R_high/R_low)+1
  - h_param_strengthened: r^τ·F·K·2^σ ≤ 66
  - Output: ν(H' fiber ∩ G) ≥ r^(6τ)/396

  Key chain:
  1. sum(S) ≥ r^(5τ)/(K·2^σ)          [from extraction bound, passed as h_sum_S]
  2. mass-half: sum(T_conc) ≥ sum(S)/2 ≥ r^(5τ)/(2K·2^σ)
  3. concentration: H' sum ≥ sum(T_conc)/3 ≥ r^(5τ)/(6K·2^σ)
  4. overlap ≤ F: H' union ≥ r^(5τ)/(6F·K·2^σ)
  5. h_param_strengthened: 1/(F·K·2^σ) ≥ r^τ/66
  6. H' ≥ r^(6τ)/(6·66) = r^(6τ)/396
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.ConcentratedHPrime
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- Generalized bounded overlap: separation at r/(4R_sep), distance ≥ R_dist.

    Returns overlap ≤ floor(16π·R_sep/R_dist) + 1.
    Requires r ≤ R_dist/4 (Case 1 of the packing argument). -/
lemma source_tubes_bounded_overlap_F
    (x : Point) (r R_low R_high : ℝ)
    (hr : 0 < r) (hR_low : 0 < R_low) (hR_high : 0 < R_high)
    (hr_small : r ≤ R_low / 4)
    (T : Finset (AffineSubspace ℝ Point))
    (h_lines : ∀ ℓ ∈ T, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (h_sep : ∀ ℓ1 ∈ T, ∀ ℓ2 ∈ T, ℓ1 ≠ ℓ2 →
      submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R_high))
    (y : Point) (hyd : dist x y ≥ R_low) :
    (T.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))).card ≤
      Nat.floor (16 * Real.pi * R_high / R_low) + 1 := by
  classical
  let T' : Finset (AffineSubspace ℝ Point) := T.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))
  have hT'_sub : T' ⊆ T := Finset.filter_subset _ _
  have h_y_ne_x : y ≠ x := by
    intro h
    have h9 : dist x y = 0 := by rw [h] <;> simp
    linarith [hR_low, hyd]
  let V0 := Submodule.span ℝ {y - x}
  have hV0 : Module.finrank ℝ V0 = 1 :=
    finrank_span_singleton (show y - x ≠ 0 from sub_ne_zero.mpr h_y_ne_x)
  let θ0 := directionAngle V0 hV0
  have h_bound : ∀ ℓ ∈ T', submoduleDirDist ℓ.direction V0 ≤ 4 * r / R_low := by
    intro ℓ hℓ
    have hℓT : ℓ ∈ T := hT'_sub hℓ
    have h_y_in : y ∈ Metric.thickening r (ℓ : Set Point) := (Finset.mem_filter.mp hℓ).2
    let L : Line2 := ⟨ℓ, (h_lines ℓ hℓT).2⟩
    have h_x_on : x ∈ (ℓ : Set Point) := (h_lines ℓ hℓT).1
    have h_x_in_2tube : x ∈ tube (2 * r) L := by
      have h : x ∈ (L.toSet) := h_x_on
      exact Metric.mem_thickening_iff.mpr ⟨x, h, by simp [infDist_lt_iff, hr]⟩
    have h_y_in_2tube : y ∈ tube (2 * r) L := by
      rcases Metric.mem_thickening_iff.mp h_y_in with ⟨z, hz, hdist⟩
      exact Metric.mem_thickening_iff.mpr ⟨z, hz, by linarith⟩
    have h_main := direction_closeness r hr L x y h_y_ne_x h_x_in_2tube h_y_in_2tube
    have h_norm : ‖y - x‖ ≥ R_low := by
      have h10 : dist x y = ‖x - y‖ := by rfl
      have h11 : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
      linarith
    calc
      submoduleDirDist ℓ.direction V0
        = submoduleDirDist L.toAffine.direction V0 := by rfl
      _ ≤ 4 * r / ‖y - x‖ := h_main
      _ ≤ 4 * r / R_low := by gcongr
  let ψ : {ℓ // ℓ ∈ T'} → ℝ := fun p =>
    modPiHalf (directionAngle p.val.direction (h_lines p.val (hT'_sub p.property)).2 - θ0)
  have h_abs_sin : ∀ p, |Real.sin (ψ p)| = submoduleDirDist p.val.direction V0 := by
    intro p
    have h1 : |Real.sin (ψ p)| =
        |Real.sin (directionAngle p.val.direction (h_lines p.val (hT'_sub p.property)).2 - θ0)| := by
      simp [ψ, abs_sin_modPiHalf]
    rw [h1, dirDist_eq_abs_sin p.val.direction V0
      (h_lines p.val (hT'_sub p.property)).2 hV0] <;> rfl
  have hψ_abs_pi2 : ∀ p, |ψ p| ≤ Real.pi / 2 := fun p => modPiHalf_abs_bounds _
  have h_r_div_R : r / R_low ≤ 1 / 4 := by
    have h1 : r ≤ R_low / 4 := hr_small
    have h2 : 0 < R_low := hR_low
    calc r / R_low ≤ (R_low / 4) / R_low := by gcongr
         _ = 1 / 4 := by field_simp [h2.ne'] <;> ring
  have hψ_bounds : ∀ p, -(2 * Real.pi * r / R_low) ≤ ψ p ∧ ψ p ≤ 2 * Real.pi * r / R_low := by
    intro p
    have h1 : |Real.sin (ψ p)| ≤ 4 * r / R_low := by
      rw [h_abs_sin p] <;> exact h_bound p.val p.property
    have h2 : |ψ p| ≤ Real.pi / 2 := hψ_abs_pi2 p
    have h3 : (2 / Real.pi) * |ψ p| ≤ |Real.sin (ψ p)| := Real.mul_abs_le_abs_sin h2
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have h4 : |ψ p| ≤ 2 * Real.pi * r / R_low := by
      have h5 : |ψ p| = (Real.pi / 2) * ((2 / Real.pi) * |ψ p|) := by
        field_simp [hpi_ne] <;> ring
      rw [h5]
      have h6 : (Real.pi / 2) * ((2 / Real.pi) * |ψ p|) ≤ (Real.pi / 2) * |Real.sin (ψ p)| :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h7 : (Real.pi / 2) * |Real.sin (ψ p)| ≤ (Real.pi / 2) * (4 * r / R_low) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h8 : (Real.pi / 2) * (4 * r / R_low) = 2 * Real.pi * r / R_low := by ring
      rw [h8] at h7
      exact le_trans h6 h7
    exact ⟨by linarith [abs_le.mp h4], by linarith [abs_le.mp h4]⟩
  have h_inj : Set.InjOn ψ (T'.attach : Set {ℓ // ℓ ∈ T'}) := by
    intro p1 hp1 p2 hp2 h_eq
    by_contra hne
    have hne_val : p1.val ≠ p2.val := by intro h; apply hne; exact Subtype.ext h
    have hℓ1T : p1.val ∈ T := hT'_sub p1.property
    have hℓ2T : p2.val ∈ T := hT'_sub p2.property
    have h_sep' : submoduleDirDist p1.val.direction p2.val.direction ≥ r / (4 * R_high) :=
      h_sep p1.val hℓ1T p2.val hℓ2T hne_val
    have h11 : |Real.sin (ψ p1 - ψ p2)| =
        |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| := by
      have h_simp : ψ p1 - ψ p2 =
          modPiHalf (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
          modPiHalf (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) := by rfl
      rw [h_simp]
      have h := abs_sin_sub_modPiHalf
        (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0)
        (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0)
      have h_alg : (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
          (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) =
          directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 := by ring
      rw [h_alg] at h; exact h
    have h12 : |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
        directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| =
        submoduleDirDist p1.val.direction p2.val.direction := by
      rw [dirDist_eq_abs_sin p1.val.direction p2.val.direction
        (h_lines p1.val hℓ1T).2 (h_lines p2.val hℓ2T).2] <;> rfl
    have h13 : |Real.sin (ψ p1 - ψ p2)| = 0 := by rw [h_eq] <;> simp
    rw [h11, h12] at h13
    have h14 : submoduleDirDist p1.val.direction p2.val.direction = 0 := by simpa using h13
    have h_pos : 0 < r / (4 * R_high) := by positivity
    rw [h14] at h_sep'
    have h_contra : (0 : ℝ) ≥ r / (4 * R_high) := h_sep'
    exact False.elim (not_le.mpr h_pos h_contra)
  have h_card_attach : T'.attach.card = T'.card := by simp
  let s : Finset ℝ := T'.attach.image ψ
  have h_card_s : s.card = T'.card := by
    rw [Finset.card_image_of_injOn h_inj, h_card_attach]
  let φ : ℝ → ℝ := fun z => z + 2 * Real.pi * r / R_low
  let s' : Finset ℝ := s.image φ
  have hφ_inj : Set.InjOn φ (s : Set ℝ) := by intro z1 _ z2 _ h; simpa [φ] using h
  have h_card_s' : s'.card = s.card := by rw [Finset.card_image_of_injOn hφ_inj]
  have h_lo : ∀ z ∈ s', 0 ≤ z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
    have h7 : -(2 * Real.pi * r / R_low) ≤ ψ p := (hψ_bounds p).1
    have h9 : 0 ≤ ψ p + 2 * Real.pi * r / R_low := by linarith
    simpa [φ] using h9
  have h_hi : ∀ z ∈ s', z ≤ 4 * Real.pi * r / R_low := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
    have h7 : ψ p ≤ 2 * Real.pi * r / R_low := (hψ_bounds p).2
    have h_nonneg : 0 ≤ 2 * Real.pi * r / R_low := by positivity
    have h9 : ψ p + 2 * Real.pi * r / R_low ≤ 4 * Real.pi * r / R_low := by
      calc ψ p + 2 * Real.pi * r / R_low
        ≤ 2 * Real.pi * r / R_low + 2 * Real.pi * r / R_low := by gcongr
      _ = 4 * Real.pi * r / R_low := by ring
    simpa [φ] using h9
  have h_sep_s' : ∀ z1 ∈ s', ∀ z2 ∈ s', z1 ≠ z2 → |z1 - z2| ≥ r / (4 * R_high) := by
    intro z1 hz1 z2 hz2 hne
    rcases Finset.mem_image.mp hz1 with ⟨w1, hw1, rfl⟩
    rcases Finset.mem_image.mp hz2 with ⟨w2, hw2, rfl⟩
    have hne2 : w1 ≠ w2 := by intro h; apply hne; simp [h]
    rcases Finset.mem_image.mp hw1 with ⟨p1, _, rfl⟩
    rcases Finset.mem_image.mp hw2 with ⟨p2, _, rfl⟩
    have hne3 : p1 ≠ p2 := by intro h; apply hne2; rw [h]
    have hℓ1T : p1.val ∈ T := hT'_sub p1.property
    have hℓ2T : p2.val ∈ T := hT'_sub p2.property
    have h_sep' : submoduleDirDist p1.val.direction p2.val.direction ≥ r / (4 * R_high) :=
      h_sep p1.val hℓ1T p2.val hℓ2T (by exact_mod_cast hne3)
    have h14 : |Real.sin (ψ p1 - ψ p2)| ≥ r / (4 * R_high) := by
      have h11 : |Real.sin (ψ p1 - ψ p2)| =
          |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| := by
        have h_simp : ψ p1 - ψ p2 =
            modPiHalf (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            modPiHalf (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) := by rfl
        rw [h_simp]
        have h := abs_sin_sub_modPiHalf
          (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0)
          (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0)
        have h_alg : (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) =
            directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 := by ring
        rw [h_alg] at h; exact h
      have h12 : |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| =
          submoduleDirDist p1.val.direction p2.val.direction := by
        rw [dirDist_eq_abs_sin p1.val.direction p2.val.direction
          (h_lines p1.val hℓ1T).2 (h_lines p2.val hℓ2T).2] <;> rfl
      rw [h11, h12] <;> exact h_sep'
    have h14' : |ψ p1 - ψ p2| ≤ Real.pi := by
      have h15 : |ψ p1| ≤ 2 * Real.pi * r / R_low :=
        abs_le.mpr ⟨(hψ_bounds p1).1, (hψ_bounds p1).2⟩
      have h16 : |ψ p2| ≤ 2 * Real.pi * r / R_low :=
        abs_le.mpr ⟨(hψ_bounds p2).1, (hψ_bounds p2).2⟩
      calc |ψ p1 - ψ p2|
        ≤ |ψ p1| + |ψ p2| := abs_sub _ _
      _ ≤ 2 * Real.pi * r / R_low + |ψ p2| := by gcongr
      _ ≤ 2 * Real.pi * r / R_low + 2 * Real.pi * r / R_low := by gcongr
      _ = 4 * Real.pi * r / R_low := by ring
      _ ≤ Real.pi := by
        have h17 : 4 * Real.pi * r / R_low ≤ Real.pi := by
          have h18 : r / R_low ≤ 1 / 4 := h_r_div_R
          calc 4 * Real.pi * r / R_low
            = 4 * Real.pi * (r / R_low) := by ring
          _ ≤ 4 * Real.pi * (1 / 4) := by gcongr
          _ = Real.pi := by ring
        exact h17
    have h17 : |Real.sin (ψ p1 - ψ p2)| ≤ |ψ p1 - ψ p2| := Real.abs_sin_le_abs
    have h21 : |φ (ψ p1) - φ (ψ p2)| = |ψ p1 - ψ p2| := by simp [φ] <;> abel
    rw [h21]; exact le_trans h14 h17
  have h_pack := real_packing_simple (show 0 < r / (4 * R_high) by positivity)
    (show 0 ≤ 4 * Real.pi * r / R_low by positivity) h_lo h_hi h_sep_s'
  rw [h_card_s', h_card_s] at h_pack
  have h_final : (T'.card : ℝ) ≤ (16 * Real.pi * R_high / R_low) + 1 := by
    have h22 : (T'.card : ℝ) ≤ (4 * Real.pi * r / R_low) / (r / (4 * R_high)) + 1 := by
      have h23 : T'.card ≤ Nat.floor ((4 * Real.pi * r / R_low) / (r / (4 * R_high))) + 1 := h_pack
      have h241 : 0 ≤ (4 * Real.pi * r / R_low) / (r / (4 * R_high)) := by positivity
      have h24 : (Nat.floor ((4 * Real.pi * r / R_low) / (r / (4 * R_high))) : ℝ) ≤
          (4 * Real.pi * r / R_low) / (r / (4 * R_high)) := Nat.floor_le h241
      have h23' : (T'.card : ℝ) ≤ (Nat.floor ((4 * Real.pi * r / R_low) / (r / (4 * R_high))) : ℝ) + 1 := by
        exact_mod_cast h23
      calc (T'.card : ℝ)
        ≤ (Nat.floor ((4 * Real.pi * r / R_low) / (r / (4 * R_high))) : ℝ) + 1 := h23'
      _ ≤ (4 * Real.pi * r / R_low) / (r / (4 * R_high)) + 1 := by gcongr
    have h25 : (4 * Real.pi * r / R_low) / (r / (4 * R_high)) = 16 * Real.pi * R_high / R_low := by
      field_simp [hr.ne', hR_low.ne', hR_high.ne'] <;> ring
    rw [h25] at h22; exact h22
  have hX_pos : 0 ≤ 16 * Real.pi * R_high / R_low := by positivity
  by_cases h0 : T'.card = 0
  · rw [h0]; simp
  · have h_pos : 0 < T'.card := Nat.pos_of_ne_zero h0
    have h1 : ((T'.card - 1 : ℕ) : ℝ) ≤ 16 * Real.pi * R_high / R_low := by
      have h3 : ((T'.card - 1 : ℕ) : ℝ) = (T'.card : ℝ) - 1 := by
        simp [Nat.cast_sub h_pos] <;> norm_num
      rw [h3]; linarith [h_final]
    have h2 : T'.card - 1 ≤ Nat.floor (16 * Real.pi * R_high / R_low) := by
      by_contra h4
      have h5 : (T'.card - 1 : ℕ) > Nat.floor (16 * Real.pi * R_high / R_low) := by omega
      have h6 : ((T'.card - 1 : ℕ) : ℝ) ≥ (Nat.floor (16 * Real.pi * R_high / R_low) : ℝ) + 1 := by
        exact_mod_cast h5
      have h7 : 16 * Real.pi * R_high / R_low < (Nat.floor (16 * Real.pi * R_high / R_low) : ℝ) + 1 :=
        Nat.lt_floor_add_one (16 * Real.pi * R_high / R_low)
      have h8 : ((T'.card - 1 : ℕ) : ℝ) > 16 * Real.pi * R_high / R_low := by linarith
      exact not_le.mpr h8 h1
    have h9 : T'.card ≤ Nat.floor (16 * Real.pi * R_high / R_low) + 1 := by omega
    exact h9

/-- H' fiber lower bound using mass-half of direction-separated S.

    Unlike `concentrated_H'_fiber_lower_mass`, this takes mass-half of S
    (not T_x) and uses the extraction-derived lower bound on ∑_S.
    The overlap constant F cancels with h_param_strengthened to yield
    the same r^(6τ)/396 bound needed by the two-ends contradiction. -/
lemma concentrated_H'_fiber_lower_mass_S
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r R_low R_high κ σ τ threshold K : ℝ)
    (hr : 0 < r) (hR_low : 0 < R_low) (hR_high : 0 < R_high)
    (hr_small : r ≤ R_low / 4)
    (hκ_pos : 0 < Real.rpow r κ)
    (hthreshold_nonneg : 0 ≤ threshold)
    (hthreshold_lt : threshold < (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ))
    (x : Point)
    (S T_conc : Finset (AffineSubspace ℝ Point))
    (Y_x : Set Point) (hY_meas : MeasurableSet Y_x)
    (h_lines : ∀ ℓ ∈ S, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (hY_sub_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G})
    (h_mass_lower : ∀ ℓ ∈ S,
      ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤
        ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x))
    (h_sep : ∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
      submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R_high))
    (hTconc_sub : T_conc ⊆ S)
    (h_conc : ∀ ℓ ∈ T_conc,
      IsConcentrated ν₂ Y_x (Metric.thickening r (ℓ : Set Point)) r κ)
    (hT_conc_sum_lower : ∑ ℓ ∈ T_conc, ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
      ENNReal.ofReal (Real.rpow r (5 * τ) / (2 * K * (2 : ℝ)^σ)))
    (y_dist : ∀ (z : Point), z ∈ Y_x → dist x z ≥ R_low)
    (F : ℕ)
    (hF_def : F = Nat.floor (16 * Real.pi * R_high / R_low) + 1)
    (hK_pos : 0 < K) (hσ : 0 ≤ σ) (hτ : 0 < τ)
    (h_param_strengthened : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ ≤ 66) :
    ν₂ ({y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩
        {b₂ | (x, b₂) ∈ G}) ≥
      ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := by
  classical
  choose c hc using fun ℓ hℓ => h_conc ℓ hℓ
  let c_total (ℓ : AffineSubspace ℝ Point) : Point :=
    if h : ℓ ∈ T_conc then c ℓ h else (0 : Point)
  let A (ℓ : AffineSubspace ℝ Point) : Set Point :=
    Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩ Y_x
  have hc_total : ∀ (ℓ : AffineSubspace ℝ Point), ∀ (hℓ : ℓ ∈ T_conc),
      c_total ℓ = c ℓ hℓ := by
    intro ℓ hℓ
    simp [c_total, hℓ]
  have hA_meas : ∀ ℓ ∈ T_conc, MeasurableSet (A ℓ) := by
    intro ℓ _
    exact (Metric.isOpen_thickening.measurableSet).inter
      (isOpen_ball.measurableSet) |>.inter hY_meas
  let tube_mass (ℓ : AffineSubspace ℝ Point) : ENNReal :=
    ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x)
  have hA_mass_actual : ∀ ℓ ∈ T_conc,
      ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * tube_mass ℓ := by
    intro ℓ hℓ
    have hct : c_total ℓ = c ℓ hℓ := hc_total ℓ hℓ
    have hA_eq : A ℓ = Metric.thickening r (ℓ : Set Point) ∩
        Metric.ball (c ℓ hℓ) (Real.rpow r κ) ∩ Y_x := by
      unfold A
      rw [hct] <;> rfl
    rw [hA_eq]
    exact hc ℓ hℓ
  have hA_sub_H' : ∀ ℓ ∈ T_conc, A ℓ ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro ℓ hℓ y hy
    have h6 : y ∈ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) := hy.1
    have h7 : y ∈ Y_x := hy.2
    rcases exists_normal_of_affineSubspace x ℓ (h_lines ℓ (hTconc_sub hℓ)).1
        (h_lines ℓ (hTconc_sub hℓ)).2 with ⟨n, hℓ_eq⟩
    have h10 : tubeOfNormal r x n = Metric.thickening r (ℓ : Set Point) := by
      rw [hℓ_eq]; exact tubeOfNormal_eq_thickening r hr x n
    have h11 : A ℓ ⊆ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G} := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2⟩, hY_sub_G hz.2⟩
    have h12 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G}) ≥ ν₂ (A ℓ) := measure_mono h11
    have h13 : ν₂ (A ℓ) ≥ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
      have h1 : ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * tube_mass ℓ := hA_mass_actual ℓ hℓ
      have h2 : tube_mass ℓ ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) :=
        h_mass_lower ℓ (hTconc_sub hℓ)
      have h3 : (1 / 3 : ENNReal) * tube_mass ℓ ≥
          (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by gcongr
      have h4 : (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) =
          ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
        have h41 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) =
            ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h41]
        have h42 : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ENNReal) := by
          have h : ENNReal.ofReal ((1 : ℝ) / 3) = ENNReal.ofReal (1 : ℝ) / ENNReal.ofReal (3 : ℝ) :=
            ENNReal.ofReal_div_of_pos (by norm_num)
          rw [h]
          have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
          have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ENNReal) := by simp
          rw [h2, h3] <;> rfl
        rw [h42] <;> ring
      rw [h4] at h3
      exact le_trans h3 h1
    have h14 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) > ENNReal.ofReal threshold := by
      have h141 : 0 ≤ threshold := hthreshold_nonneg
      have h142 : 0 ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by
        apply mul_nonneg
        · norm_num
        · exact Real.rpow_nonneg hr.le _
      have h_iff : ENNReal.ofReal threshold ≤ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
          threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
        ENNReal.ofReal_le_ofReal_iff h142
      have h_le : threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by linarith
      have h_ne : ENNReal.ofReal threshold ≠ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
        intro h
        have h_iff2 : ENNReal.ofReal threshold = ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
            threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
          ENNReal.ofReal_eq_ofReal_iff h141 h142
        have h_eq : threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := h_iff2.mp h
        linarith
      exact (h_iff.mpr h_le).lt_of_ne h_ne
    have h15 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold :=
      lt_of_lt_of_le h14 (le_trans h13 h12)
    have h15' : ν₂ (tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold := by
      rw [h10]; exact h15
    have h18 : y ∈ tubeOfNormal r x n := by rw [h10]; exact h6.1
    have h16 : y ∈ tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) :=
      ⟨h18, h6.2⟩
    exact ⟨n, c_total ℓ, h15', h16⟩
  let U : Set Point := ⋃ ℓ ∈ T_conc, A ℓ
  have hU_meas : MeasurableSet U :=
    Finset.measurableSet_biUnion T_conc hA_meas
  have hU_sub : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, hℓ, hyA⟩
    exact hA_sub_H' ℓ hℓ hyA
  have hU_sub_G : U ⊆ {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, _, hyA⟩
    have h_in_Y : y ∈ Y_x := hyA.2
    exact hY_sub_G h_in_Y
  have hU_sub' : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩
      {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    exact ⟨hU_sub hy, hU_sub_G hy⟩
  -- Overlap bound ≤ F
  have h_overlap : ∀ y : Point, (T_conc.filter (fun ℓ => y ∈ A ℓ)).card ≤ F := by
    intro y
    by_cases hyY : y ∈ Y_x
    · let S_y : Finset (AffineSubspace ℝ Point) :=
        T_conc.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))
      have hS1 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) ⊆ S_y := by
        intro ℓ hℓ
        have h3 : ℓ ∈ T_conc := (Finset.mem_filter.mp hℓ).1
        have h2 : y ∈ A ℓ := (Finset.mem_filter.mp hℓ).2
        have h4 : y ∈ Metric.thickening r (ℓ : Set Point) := h2.1.1
        exact Finset.mem_filter.mpr ⟨h3, h4⟩
      have hS2 : S_y.card ≤ F := by
        rw [hF_def]
        exact source_tubes_bounded_overlap_F x r R_low R_high hr hR_low hR_high hr_small
          T_conc (fun ℓ hℓ => h_lines ℓ (hTconc_sub hℓ))
          (fun ℓ1 hℓ1 ℓ2 hℓ2 hne => h_sep ℓ1 (hTconc_sub hℓ1) ℓ2 (hTconc_sub hℓ2) hne)
          y (y_dist y hyY)
      exact le_trans (Finset.card_le_card hS1) hS2
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ _ h6
        exact hyY h6.2
      rw [h5] <;> simp
  -- Sum = integral of overlap count
  have h_sum_eq : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) =
      ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
    have h1 : ∀ ℓ ∈ T_conc, ν₂ (A ℓ) =
        ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
      intro ℓ hℓ
      have h2 : ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ = ν₂ (A ℓ) := by
        rw [MeasureTheory.lintegral_indicator (hA_meas ℓ hℓ)]
        have h3 : ∫⁻ y, (1 : ENNReal) ∂(ν₂.restrict (A ℓ)) = ν₂ (A ℓ) := by simp
        exact h3
      exact h2.symm
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∑ ℓ ∈ T_conc, ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          apply Finset.sum_congr rfl; intro ℓ hℓ; exact h1 ℓ hℓ
      _ = ∫⁻ y, ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          have h_ind_meas : ∀ ℓ ∈ T_conc, Measurable (Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal))) :=
            fun ℓ hℓ => measurable_const.indicator (hA_meas ℓ hℓ)
          exact (MeasureTheory.lintegral_finsetSum T_conc h_ind_meas).symm
      _ = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
          have h_pointwise : ∀ (y : Point), ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
              ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) := by
            intro y
            have h_eq1 : ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
                ∑ ℓ ∈ T_conc, (if y ∈ A ℓ then (1 : ENNReal) else 0) := by
              apply Finset.sum_congr rfl
              intro ℓ _
              simp [Set.indicator_apply] <;> split_ifs <;> simp
            rw [h_eq1, Finset.sum_boole] <;> simp
          congr with y
          exact h_pointwise y
  have h_overlap_indicator : ∀ (y : Point),
      ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤
      (F : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y := by
    intro y
    by_cases hyU : y ∈ U
    · have h3 : ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤ (F : ENNReal) := by
        exact_mod_cast h_overlap y
      have h4 : Set.indicator U (fun _ => (1 : ENNReal)) y = 1 := by
        rw [Set.indicator_of_mem hyU] <;> simp
      rw [h4] <;> simpa using h3
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ hℓ h6
        have h7 : y ∈ U := Set.mem_iUnion₂.mpr ⟨ℓ, hℓ, h6⟩
        exact hyU h7
      rw [h5] <;> simp [Set.indicator_apply, hyU] <;> norm_num
  have h_sum : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≤ (F : ENNReal) * ν₂ U := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := h_sum_eq
      _ ≤ ∫⁻ y, (F : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
          apply lintegral_mono; exact h_overlap_indicator
      _ = (F : ENNReal) * ν₂ U := by
          have h_cmul : ∫⁻ y, (F : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ =
              (F : ENNReal) * ∫⁻ y, Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
            apply MeasureTheory.lintegral_const_mul (F : ENNReal) (hf := measurable_const.indicator hU_meas)
          rw [h_cmul]
          have h_ind_U : ∫⁻ a, Set.indicator U (fun _ => (1 : ENNReal)) a ∂ν₂ = ν₂ U := by
            rw [MeasureTheory.lintegral_indicator hU_meas]
            have h : ∫⁻ a, (1 : ENNReal) ∂(ν₂.restrict U) = ν₂ U := by simp
            exact h
          rw [h_ind_U]
  -- Mass chain: concentration gives 1/3 of tube mass, and hT_conc_sum_lower gives the bound
  have h_sum_lower1 : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        ≥ ∑ ℓ ∈ T_conc, ((1 / 3 : ENNReal) * tube_mass ℓ) :=
          Finset.sum_le_sum fun ℓ hℓ => hA_mass_actual ℓ hℓ
      _ = (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := by
        rw [Finset.mul_sum]
  have h_rpow5_pos : 0 < Real.rpow r (5 * τ) := Real.rpow_pos_of_pos hr (5 * τ)
  have h_K2σ_pos : 0 < K * (2 : ℝ)^σ := by positivity
  set Y2 : ℝ := Real.rpow r (5 * τ) / (2 * K * (2 : ℝ)^σ) with hY2_def
  have h_sum_final : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥
      ENNReal.ofReal (Real.rpow r (5 * τ) / (6 * K * (2 : ℝ)^σ)) := by
    have h1 : (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ ≥
        (1 / 3 : ENNReal) * ENNReal.ofReal Y2 := by gcongr
    have h2 : (1 / 3 : ENNReal) * ENNReal.ofReal Y2 =
        ENNReal.ofReal ((1 / 3 : ℝ) * Y2) := by
      have h_third : (1 / 3 : ENNReal) = ENNReal.ofReal (1 / 3 : ℝ) := by
        have h : ENNReal.ofReal ((1 : ℝ) / 3) = ENNReal.ofReal (1 : ℝ) / ENNReal.ofReal (3 : ℝ) :=
          ENNReal.ofReal_div_of_pos (by norm_num)
        rw [h]
        have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
        have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ENNReal) := by simp
        rw [h2, h3] <;> rfl
      rw [h_third]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    have h3 : (1 / 3 : ℝ) * Y2 = Real.rpow r (5 * τ) / (6 * K * (2 : ℝ)^σ) := by
      simp [hY2_def] <;> ring
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        ≥ (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := h_sum_lower1
      _ ≥ (1 / 3 : ENNReal) * ENNReal.ofReal Y2 := h1
      _ = ENNReal.ofReal ((1 / 3 : ℝ) * Y2) := h2
      _ = ENNReal.ofReal (Real.rpow r (5 * τ) / (6 * K * (2 : ℝ)^σ)) := by rw [h3]
  -- Final algebra: use h_param_strengthened to get r^(6τ)/396
  have hF_pos : 0 < F := by omega
  have h_ineq1 : Real.rpow r (5 * τ) / (6 * (F : ℝ) * K * (2 : ℝ)^σ) ≥
      (1 / 396 : ℝ) * Real.rpow r (6 * τ) := by
    have h1 : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    have h2 : 0 < (F : ℝ) := by exact_mod_cast hF_pos
    have h3 : 0 < K * (2 : ℝ)^σ := by positivity
    have h4 : Real.rpow r (6 * τ) = Real.rpow r (5 * τ) * Real.rpow r τ := by
      have h5 : (5 * τ) + τ = 6 * τ := by ring
      have h6 : Real.rpow r ((5 * τ) + τ) = Real.rpow r (5 * τ) * Real.rpow r τ :=
        Real.rpow_add hr (5 * τ) τ
      rw [h5] at h6
      exact h6
    have h5 : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ ≤ 66 := h_param_strengthened
    have h_denom : 0 < (F : ℝ) * K * (2 : ℝ)^σ := by positivity
    have h6 : Real.rpow r τ / 66 ≤ 1 / ((F : ℝ) * K * (2 : ℝ)^σ) := by
      have h6a : Real.rpow r τ ≤ 66 / ((F : ℝ) * K * (2 : ℝ)^σ) := by
        have h5' : Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ) ≤ 66 := by
          simpa [mul_assoc] using h5
        have h_div : (Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ)) / ((F : ℝ) * K * (2 : ℝ)^σ) ≤
            66 / ((F : ℝ) * K * (2 : ℝ)^σ) := by gcongr
        have h_cancel : (Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ)) / ((F : ℝ) * K * (2 : ℝ)^σ) =
            Real.rpow r τ := by
          field_simp [h_denom.ne'] <;> ring
        rw [h_cancel] at h_div
        exact h_div
      calc Real.rpow r τ / 66
        ≤ (66 / ((F : ℝ) * K * (2 : ℝ)^σ)) / 66 := by gcongr
      _ = 1 / ((F : ℝ) * K * (2 : ℝ)^σ) := by
        field_simp [h_denom.ne'] <;> ring
    have h7 : 1 / (6 * (F : ℝ) * K * (2 : ℝ)^σ) ≥ Real.rpow r τ / 396 := by
      calc 1 / (6 * (F : ℝ) * K * (2 : ℝ)^σ)
        = (1 / 6 : ℝ) * (1 / ((F : ℝ) * K * (2 : ℝ)^σ)) := by ring
      _ ≥ (1 / 6 : ℝ) * (Real.rpow r τ / 66) := by gcongr
      _ = Real.rpow r τ / 396 := by ring
    have h9 : 0 ≤ Real.rpow r (5 * τ) := by positivity
    have h8 : Real.rpow r (5 * τ) / (6 * (F : ℝ) * K * (2 : ℝ)^σ) ≥
        Real.rpow r (5 * τ) * (Real.rpow r τ / 396) := by
      have h81 : Real.rpow r (5 * τ) / (6 * (F : ℝ) * K * (2 : ℝ)^σ) =
          Real.rpow r (5 * τ) * (1 / (6 * (F : ℝ) * K * (2 : ℝ)^σ)) := by ring
      rw [h81]
      exact mul_le_mul_of_nonneg_left h7 h9
    have h10 : Real.rpow r (5 * τ) * (Real.rpow r τ / 396) =
        (1 / 396 : ℝ) * Real.rpow r (6 * τ) := by
      rw [h4] <;> ring
    linarith [h8, h10]
  have h_main : ν₂ U ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := by
    have h_div : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / (F : ENNReal) ≤ ν₂ U := by
      have h9 : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / (F : ENNReal) ≤ ((F : ENNReal) * ν₂ U) / (F : ENNReal) := by gcongr
      have h10 : ((F : ENNReal) * ν₂ U) / (F : ENNReal) = ν₂ U := by
        rw [mul_comm (F : ENNReal) (ν₂ U)]
        have hF_ne_zero : (F : ENNReal) ≠ 0 :=
          Nat.cast_ne_zero.mpr (ne_of_gt hF_pos)
        have hF_ne_top : (F : ENNReal) ≠ ⊤ := by simp
        exact ENNReal.mul_div_cancel_right hF_ne_zero hF_ne_top
      rw [h10] at h9
      exact h9
    set X : ℝ := Real.rpow r (5 * τ) / (6 * K * (2 : ℝ)^σ) with hX_def
    set Y : ℝ := Real.rpow r (5 * τ) / (6 * (F : ℝ) * K * (2 : ℝ)^σ) with hY_def
    have hXY : X / (F : ℝ) = Y := by
      simp [hX_def, hY_def] <;> ring
    have h_posF : 0 < (F : ℝ) := by exact_mod_cast hF_pos
    have hF_real : (F : ENNReal) = ENNReal.ofReal (F : ℝ) := by simp
    have h_div2 : ENNReal.ofReal X / (F : ENNReal) = ENNReal.ofReal Y := by
      rw [hF_real, ← ENNReal.ofReal_div_of_pos h_posF, hXY]
    have h12 : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥ ENNReal.ofReal X := h_sum_final
    have h13 : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / (F : ENNReal) ≥ ENNReal.ofReal X / (F : ENNReal) := by gcongr
    have h11 : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / (F : ENNReal) ≥ ENNReal.ofReal Y := by
      rw [h_div2] at h13
      exact h13
    have h_nonnegY : 0 ≤ Y := by
      simp [hY_def] <;> positivity
    have h_ineq2 : (1 / 396 : ℝ) * Real.rpow r (6 * τ) ≤ Y := h_ineq1
    have h_last : ENNReal.ofReal Y ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := by
      exact (ENNReal.ofReal_le_ofReal_iff h_nonnegY).mpr h_ineq2
    calc
      ν₂ U
        ≥ (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / (F : ENNReal) := h_div
      _ ≥ ENNReal.ofReal Y := h11
      _ ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := h_last
  exact le_trans h_main (measure_mono hU_sub')

end RadialBootstrapping
