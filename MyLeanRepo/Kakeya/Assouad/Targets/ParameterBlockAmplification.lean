import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationHelpers

/-!
WZ2 Section 7: amplify one full local Katz--Tao parameter pattern by
pairwise-disjoint translations, preserving the global fine-scale Katz--Tao
bound and recovering the full fine-scale cardinality.
-/

namespace Kakeya.Assouad


theorem parameter_block_amplification :
    ParameterBlockAmplificationStatement := by
  intro fineScale blockScale ktExponent s
        hfine hfine_block hblock
        hkt_pos hkt_one hs hs_kt
        localCenter hcenter localPoints hnonempty hcontain hkt hcard

  have hblock_pos : 0 < blockScale := by linarith
  have hblock_lt_one : blockScale < 1 := by linarith

  set h : ℝ := Real.rpow blockScale (1 / 3 : ℝ) with hdef
  set R : ℝ := 1 / 2 - blockScale / 10 with Rdef

  have h_pos : 0 < h := Real.rpow_pos_of_pos hblock_pos _
  have R_pos : 0 < R := by linarith [hblock]

  have h_cube : h ^ 3 = blockScale := by
    have h_expand : Real.rpow blockScale ((1 / 3 : ℝ) * (3 : ℝ)) =
        Real.rpow (Real.rpow blockScale (1 / 3 : ℝ)) 3 :=
      Real.rpow_mul (by linarith) (1 / 3 : ℝ) (3 : ℝ)
    have h_nat : Real.rpow (Real.rpow blockScale (1 / 3 : ℝ)) 3 =
        (Real.rpow blockScale (1 / 3 : ℝ)) ^ 3 := by
      simp [Real.rpow_natCast] <;> norm_cast
    have h_eq : (Real.rpow blockScale (1 / 3 : ℝ)) ^ 3 =
        Real.rpow blockScale ((1 / 3 : ℝ) * (3 : ℝ)) :=
      (h_expand.trans h_nat).symm
    calc
      h ^ 3 = (Real.rpow blockScale (1 / 3 : ℝ)) ^ 3 := by rw [hdef]
      _ = Real.rpow blockScale ((1 / 3 : ℝ) * (3 : ℝ)) := h_eq
      _ = blockScale := by norm_num

  have h_gt_blockScale5 : blockScale / 5 < h := by
    have h_log_neg : Real.log blockScale < 0 := by
      apply Real.log_neg <;> linarith
    have h_rpow_log : ∀ (t : ℝ), Real.log (Real.rpow blockScale t) = t * Real.log blockScale := by
      intro t
      exact Real.log_rpow hblock_pos t
    have h_pos_13 : 0 < Real.rpow blockScale (1 / 3 : ℝ) := Real.rpow_pos_of_pos hblock_pos _
    have h3 : blockScale < Real.rpow blockScale (1 / 3 : ℝ) := by
      have h_pos1 : 0 < Real.rpow blockScale 1 := Real.rpow_pos_of_pos hblock_pos _
      have h_log1 : Real.log (Real.rpow blockScale 1) = (1 : ℝ) * Real.log blockScale := h_rpow_log 1
      have h_log13 : Real.log (Real.rpow blockScale (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log blockScale := h_rpow_log (1 / 3 : ℝ)
      have h_ineq : (1 : ℝ) * Real.log blockScale < (1 / 3 : ℝ) * Real.log blockScale := by nlinarith
      have h_log_lt : Real.log (Real.rpow blockScale 1) < Real.log (Real.rpow blockScale (1 / 3 : ℝ)) := by
        rw [h_log1, h_log13] <;> exact h_ineq
      have h_rpow1_eq : Real.rpow blockScale 1 = blockScale := by simp
      have h : Real.rpow blockScale 1 < Real.rpow blockScale (1 / 3 : ℝ) :=
        Real.log_lt_log_iff h_pos1 h_pos_13 |>.mp h_log_lt
      rw [h_rpow1_eq] at h
      exact h
    have h4 : Real.rpow blockScale (1 / 3 : ℝ) = h := hdef.symm
    have h5 : blockScale / 5 < blockScale := by linarith
    linarith [h3, h4]

  set N : ℕ := Nat.floor (R / h) with Ndef
  set ints : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with intsdef
  let triple_to_fn : (ℤ × ℤ) × ℤ → (Fin 3 → ℤ) := fun p =>
    fun i => match i with
      | 0 => p.1.1
      | 1 => p.1.2
      | 2 => p.2
  set indices : Finset (Fin 3 → ℤ) :=
    ((ints ×ˢ ints) ×ˢ ints).image triple_to_fn with indicesdef

  let v_of_k : (Fin 3 → ℤ) → Point 3 := fun k =>
    point3 (-localCenter 0 + (k 0 : ℝ) * h)
           (-localCenter 1 + (k 1 : ℝ) * h)
           (-localCenter 2 + (k 2 : ℝ) * h)

  have h_p3 : ∀ (x y z : ℝ),
      (point3 x y z) 0 = x ∧ (point3 x y z) 1 = y ∧ (point3 x y z) 2 = z := by
    intro x y z; simp [point3]
  have v_of_k_injective : Function.Injective v_of_k := by
    intro k1 k2 heq
    have h0 : (v_of_k k1) 0 = (v_of_k k2) 0 := by rw [heq]
    have h1 : (v_of_k k1) 1 = (v_of_k k2) 1 := by rw [heq]
    have h2 : (v_of_k k1) 2 = (v_of_k k2) 2 := by rw [heq]
    have h_eq0 : -localCenter 0 + (k1 0 : ℝ) * h = -localCenter 0 + (k2 0 : ℝ) * h := by
      have e := (h_p3 (-localCenter 0 + (k1 0 : ℝ) * h) (-localCenter 1 + (k1 1 : ℝ) * h) (-localCenter 2 + (k1 2 : ℝ) * h)).1
      have e' := (h_p3 (-localCenter 0 + (k2 0 : ℝ) * h) (-localCenter 1 + (k2 1 : ℝ) * h) (-localCenter 2 + (k2 2 : ℝ) * h)).1
      rw [←e, ←e']; exact h0
    have h_eq1 : -localCenter 1 + (k1 1 : ℝ) * h = -localCenter 1 + (k2 1 : ℝ) * h := by
      have e := (h_p3 (-localCenter 0 + (k1 0 : ℝ) * h) (-localCenter 1 + (k1 1 : ℝ) * h) (-localCenter 2 + (k1 2 : ℝ) * h)).2.1
      have e' := (h_p3 (-localCenter 0 + (k2 0 : ℝ) * h) (-localCenter 1 + (k2 1 : ℝ) * h) (-localCenter 2 + (k2 2 : ℝ) * h)).2.1
      rw [←e, ←e']; exact h1
    have h_eq2 : -localCenter 2 + (k1 2 : ℝ) * h = -localCenter 2 + (k2 2 : ℝ) * h := by
      have e := (h_p3 (-localCenter 0 + (k1 0 : ℝ) * h) (-localCenter 1 + (k1 1 : ℝ) * h) (-localCenter 2 + (k1 2 : ℝ) * h)).2.2
      have e' := (h_p3 (-localCenter 0 + (k2 0 : ℝ) * h) (-localCenter 1 + (k2 1 : ℝ) * h) (-localCenter 2 + (k2 2 : ℝ) * h)).2.2
      rw [←e, ←e']; exact h2
    have h3 : (k1 0 : ℝ) = (k2 0 : ℝ) := by
      have h_cancel : (k1 0 : ℝ) * h = (k2 0 : ℝ) * h := by linarith
      exact mul_right_cancel₀ h_pos.ne' h_cancel
    have h4 : (k1 1 : ℝ) = (k2 1 : ℝ) := by
      have h_cancel : (k1 1 : ℝ) * h = (k2 1 : ℝ) * h := by linarith
      exact mul_right_cancel₀ h_pos.ne' h_cancel
    have h5 : (k1 2 : ℝ) = (k2 2 : ℝ) := by
      have h_cancel : (k1 2 : ℝ) * h = (k2 2 : ℝ) * h := by linarith
      exact mul_right_cancel₀ h_pos.ne' h_cancel
    have h6 : k1 0 = k2 0 := by exact_mod_cast h3
    have h7 : k1 1 = k2 1 := by exact_mod_cast h4
    have h8 : k1 2 = k2 2 := by exact_mod_cast h5
    funext i; fin_cases i <;> tauto

  set translations : DiscreteSet 3 := indices.image v_of_k with translationsdef
  set amplified : DiscreteSet 3 := amplifiedParameterSet localPoints translations with amplifieddef

  have triple_to_fn_injective : Function.Injective triple_to_fn := by
    intro p1 p2 h
    have h0 : p1.1.1 = p2.1.1 := by
      have h' := congr_fun h 0
      simpa [triple_to_fn] using h'
    have h1 : p1.1.2 = p2.1.2 := by
      have h' := congr_fun h 1
      simpa [triple_to_fn] using h'
    have h2 : p1.2 = p2.2 := by
      have h' := congr_fun h 2
      simpa [triple_to_fn] using h'
    simp [Prod.ext_iff] at * <;> tauto

  have ints_card : ints.card = 2 * N + 1 := by
    rw [intsdef, Int.card_Icc]
    simp [Int.toNat_of_nonneg] <;> omega

  have indices_card : indices.card = (2 * N + 1) ^ 3 := by
    rw [indicesdef, Finset.card_image_of_injective _ triple_to_fn_injective]
    simp [Finset.card_product, ints_card] <;> ring

  have translations_card : translations.card = (2 * N + 1) ^ 3 := by
    rw [translationsdef, Finset.card_image_of_injective _ v_of_k_injective, indices_card]

  have translations_nonempty : translations.Nonempty := by
    have h : indices.Nonempty := by
      refine ⟨fun _ => 0, ?_⟩
      rw [indicesdef]
      refine Finset.mem_image.mpr ⟨((0, 0), 0), ?_, ?_⟩
      · simp [intsdef] <;> omega
      · funext i; fin_cases i <;> simp [triple_to_fn]
    exact h.image _

  have h_indices_ints : ∀ k ∈ indices, ∀ i : Fin 3, k i ∈ ints := by
    intro k hk i
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ ints ×ˢ ints ∧ p.2 ∈ ints := by
      simpa [Finset.mem_product] using hp
    have h0 : p.1.1 ∈ ints := (Finset.mem_product.mp hp'.1).1
    have h1 : p.1.2 ∈ ints := (Finset.mem_product.mp hp'.1).2
    have h2 : p.2 ∈ ints := hp'.2
    fin_cases i <;> tauto

  -- Cardinality lower bound for translations
  have N_floor_le : (N : ℝ) ≤ R / h := Nat.floor_le (show 0 ≤ R / h by positivity)
  have N_floor_gt : R / h < (N : ℝ) + 1 := Nat.lt_floor_add_one (R / h)

  have translations_card_lower_real :
      Real.rpow blockScale (-1) ≤ 100000 * (((2 * N + 1 : ℕ) : ℝ)^3) := by
    by_cases h_case : h ≤ R
    · -- Case h ≤ R
      have hR1 : 1 ≤ R / h := by
        have h : 1 * h ≤ R := by linarith
        rwa [one_le_div h_pos] at *
      have N_ge1 : 1 ≤ N := by
        have h' : ((1 : ℕ) : ℝ) ≤ R / h := by exact_mod_cast hR1
        exact Nat.le_floor h'
      have hN : (N : ℝ) ≥ R / h - 1 := by linarith [N_floor_gt]
      have h2 : 2 * (N : ℝ) + 1 ≥ R / h := by linarith
      have h3 : ((2 * N + 1 : ℕ) : ℝ) ≥ R / h := by exact_mod_cast h2
      have h4 : ((2 * N + 1 : ℕ) : ℝ)^3 ≥ (R / h)^3 := by gcongr
      have h_R3_lower : R^3 ≥ 1 / 100000 := by
        have h6 : R ≥ 499 / 1000 := by linarith [hblock]
        have h7 : R^3 ≥ (499 / 1000 : ℝ)^3 := by gcongr
        have h8 : (499 / 1000 : ℝ)^3 > 1 / 100000 := by norm_num
        linarith
      have h9 : Real.rpow blockScale (-1) = 1 / blockScale := by
        simp [Real.rpow_neg_one]
      rw [h9]
      have h10 : h^3 = blockScale := h_cube
      have h11 : 1 / h^3 ≤ 100000 * (R / h)^3 := by
        have h12 : 1 ≤ 100000 * R^3 := by linarith [h_R3_lower]
        have h13 : 0 < h^3 := by positivity
        calc
          1 / h^3 = (1 : ℝ) / h^3 := by ring
          _ ≤ (100000 * R^3) / h^3 := by gcongr
          _ = 100000 * ((R / h)^3) := by ring
      have h14 : 100000 * (R / h)^3 ≤ 100000 * ((2 * N + 1 : ℕ) : ℝ)^3 :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      have h15 : 1 / h^3 ≤ 100000 * ((2 * N + 1 : ℕ) : ℝ)^3 := h11.trans h14
      rw [←h10]
      exact h15
    · -- Case h > R
      have hR : ¬(h ≤ R) := h_case
      have h_gt_R : h > R := by linarith
      have N_eq0 : N = 0 := by
        have h1 : 0 ≤ R / h := by positivity
        have h2 : R / h < 1 := by
          rw [div_lt_one h_pos] <;> linarith
        have h3 : Nat.floor (R / h) = 0 := Nat.floor_eq_zero.mpr h2
        simpa [Ndef] using h3
      rw [N_eq0]
      have h6 : blockScale > R^3 := by
        have h7 : h^3 > R^3 := by gcongr
        rw [h_cube] at *; exact h7
      have h8 : R ≥ 499 / 1000 := by linarith [hblock]
      have h9 : R^3 ≥ (499 / 1000 : ℝ)^3 := by gcongr
      have h10 : (499 / 1000 : ℝ)^3 > 1 / 100000 := by norm_num
      have h11 : blockScale > 1 / 100000 := by linarith
      have h12 : Real.rpow blockScale (-1) = 1 / blockScale := by
        simp [Real.rpow_neg_one]
      rw [h12]
      have h14 : 1 / blockScale < 100000 := by
        rw [one_div_lt (by positivity) (by positivity)]
        <;> nlinarith
      norm_num at * <;> linarith

  have translations_card_lower :
      Kakeya.realRpowENN blockScale (-1) ≤ 100000 * translations.enncard := by
    have h1 : Kakeya.realRpowENN blockScale (-1) = ENNReal.ofReal (Real.rpow blockScale (-1)) := by
      rfl
    have h2 : translations.enncard = (translations.card : ENNReal) := by rfl
    rw [h1, h2, translations_card]
    have h3 : Real.rpow blockScale (-1) ≤ 100000 * (((2 * N + 1 : ℕ) : ℝ)^3) :=
      translations_card_lower_real
    have h4 : ENNReal.ofReal (Real.rpow blockScale (-1)) ≤
        ENNReal.ofReal (100000 * (((2 * N + 1 : ℕ) : ℝ)^3)) :=
      ENNReal.ofReal_le_ofReal h3
    have h5 : ENNReal.ofReal (100000 * (((2 * N + 1 : ℕ) : ℝ)^3)) =
        (100000 : ENNReal) * (((2 * N + 1)^3 : ℕ) : ENNReal) := by
      simp [ENNReal.ofReal_mul] <;> norm_cast
    rw [h5] at h4
    exact h4

  have translations_card_upper :
      translations.enncard ≤
        8 * Kakeya.realRpowENN blockScale (-1) := by
    rw [show translations.enncard =
      (translations.card : ENNReal) by rfl, translations_card]
    have h_le_one : h ≤ 1 := by
      rw [hdef]
      exact Real.rpow_le_one hblock_pos.le hblock_lt_one.le
        (by norm_num)
    exact
      parameterBlockTranslationCardUpper
        hblock_pos h_pos h_le_one
        (by
          simp only [Rdef]
          linarith [hblock_pos])
        h_cube N_floor_le

  -- Coordinate property of v_of_k
  have v_coord : ∀ (k : Fin 3 → ℤ) (i : Fin 3),
      (v_of_k k + localCenter) i = (k i : ℝ) * h := by
    intro k i
    fin_cases i <;> simp [v_of_k, point3, EuclideanSpace.single_apply] <;> ring

  -- Half-box containment
  have half_box : ∀ (v : Point 3), v ∈ translations →
      ∀ (p : Point 3), p ∈ localPoints → ∀ (i : Fin 3), |(p + v) i| ≤ 1 / 2 := by
    intro v hv p hp i
    rcases Finset.mem_image.mp hv with ⟨k, hk, rfl⟩
    have h1 : |p i - localCenter i| ≤ dist p localCenter := by
      simpa [Real.dist_eq] using PiLp.dist_apply_le p localCenter i
    have h2 : dist p localCenter ≤ blockScale / 10 := hcontain p hp
    have h3 : |(v_of_k k + localCenter) i| ≤ R := by
      rw [v_coord k i]
      have h4 : k i ∈ ints := h_indices_ints k hk i
      simp only [intsdef, Finset.mem_Icc] at h4
      have h5 : -(N : ℤ) ≤ k i := h4.1
      have h6 : k i ≤ (N : ℤ) := h4.2
      have h7 : |(k i : ℝ)| ≤ (N : ℝ) := by
        apply abs_le.mpr
        constructor
        · exact_mod_cast h5
        · exact_mod_cast h6
      calc
        |(k i : ℝ) * h| = |(k i : ℝ)| * |h| := by rw [abs_mul]
        _ = |(k i : ℝ)| * h := by rw [abs_of_pos h_pos]
        _ ≤ (N : ℝ) * h := by
          exact mul_le_mul_of_nonneg_right h7 h_pos.le
        _ ≤ R := by
          have h8 : (N : ℝ) ≤ R / h := N_floor_le
          have h9 : (N : ℝ) * h ≤ R := by
            calc (N : ℝ) * h ≤ (R / h) * h := by gcongr
              _ = R := by field_simp [h_pos.ne'] <;> ring
          exact h9
    calc
      |(p + v_of_k k) i|
        = |(p - localCenter) i + (v_of_k k + localCenter) i| := by
          simp [Pi.add_apply] <;> ring
      _ ≤ |(p - localCenter) i| + |(v_of_k k + localCenter) i| := by
        have h_abs : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
          intro a b
          have h1 : -(|a| + |b|) ≤ a + b := by
            have h1a : -|a| ≤ a := neg_abs_le a
            have h1b : -|b| ≤ b := neg_abs_le b
            linarith
          have h2 : a + b ≤ |a| + |b| := by
            have h2a : a ≤ |a| := le_abs_self a
            have h2b : b ≤ |b| := le_abs_self b
            linarith
          exact abs_le.mpr ⟨h1, h2⟩
        exact h_abs _ _
      _ ≤ dist p localCenter + R := by
        have h_sub : (p - localCenter) i = p i - localCenter i := by
          simp [Pi.sub_apply]
        have h_coord1 : |(p - localCenter) i| ≤ dist p localCenter := by
          rw [h_sub]
          exact h1
        linarith [h3, h_coord1]
      _ ≤ blockScale / 10 + R := by gcongr
      _ = 1 / 2 := by
        simp [Rdef] <;> ring

  -- Unit ball containment
  have amplified_in_unitBall : amplified.IsInUnitBall := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
    rcases Finset.mem_image.mp hpv with ⟨q, hq, rfl⟩
    have h1 : ∀ (i : Fin 3), |(q + v) i| ≤ 1 / 2 := half_box v hv q hq
    exact half_box_implies_unit_ball (q + v) h1

  -- Half-box property for amplified
  have amplified_half : ∀ p ∈ amplified,
      |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨v, hv, hpv⟩
    rcases Finset.mem_image.mp hpv with ⟨q, hq, rfl⟩
    have h1 := half_box v hv q hq
    exact ⟨h1 0, h1 1, h1 2⟩

  -- Disjointness of translated copies
  have h_sep : ∀ v ∈ translations, ∀ w ∈ translations, v ≠ w →
      ∃ c : Fin 3, |(v - w) c| ≥ h := by
    intro v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨k1, hk1, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨k2, hk2, rfl⟩
    have h_kne : k1 ≠ k2 := by intro h; apply hne; rw [h]
    have h_exists : ∃ (i : Fin 3), k1 i ≠ k2 i := by
      by_contra h
      have h' : ∀ (i : Fin 3), k1 i = k2 i := by
        intro i
        by_contra h5
        exact h ⟨i, h5⟩
      have h_eq : k1 = k2 := funext h'
      exact h_kne h_eq
    rcases h_exists with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h_eq2 : (v_of_k k1 - v_of_k k2) i = ((k1 i : ℝ) - (k2 i : ℝ)) * h := by
      have h1 : (v_of_k k1 - v_of_k k2) i = (v_of_k k1) i - (v_of_k k2) i := by rfl
      have h2 : (v_of_k k1 + localCenter) i = (v_of_k k1) i + localCenter i := by rfl
      have h3 : (v_of_k k2 + localCenter) i = (v_of_k k2) i + localCenter i := by rfl
      rw [h1]
      have h4 : (v_of_k k1) i - (v_of_k k2) i = (v_of_k k1 + localCenter) i - (v_of_k k2 + localCenter) i := by
        rw [h2, h3] <;> ring
      rw [h4, v_coord k1 i, v_coord k2 i] <;> ring
    rw [h_eq2, abs_mul, abs_of_pos h_pos]
    have h_abs : |(k1 i : ℝ) - (k2 i : ℝ)| ≥ 1 := by
      have h_ne_int : (k1 i : ℤ) - (k2 i : ℤ) ≠ 0 := by omega
      have h_int : 1 ≤ |(k1 i : ℤ) - (k2 i : ℤ)| := Int.one_le_abs h_ne_int
      exact_mod_cast h_int
    have h_ge : |(k1 i : ℝ) - (k2 i : ℝ)| * h ≥ h := by
      have h_pos' : 0 ≤ h := h_pos.le
      have h' : |(k1 i : ℝ) - (k2 i : ℝ)| * h ≥ 1 * h :=
        mul_le_mul_of_nonneg_right h_abs h_pos'
      have h'' : (1 : ℝ) * h = h := by ring
      rw [h''] at h'
      exact h'
    exact h_ge

  have translated_disjoint : Set.PairwiseDisjoint (translations : Set (Point 3))
      (translateParameterSet localPoints) := by
    have h_helper : Set.PairwiseDisjoint (translations : Set (Point 3))
        (fun v : Point 3 => (translateParameterSet localPoints v : Set (Point 3))) :=
      translated_sets_pairwise_disjoint h_pos h_gt_blockScale5
        (localPoints_diameter hcontain) h_sep
    intro v hv w hw hne
    have h_set_disj : Disjoint ((translateParameterSet localPoints v) : Set (Point 3))
        ((translateParameterSet localPoints w) : Set (Point 3)) := h_helper hv hw hne
    have h_iff : Disjoint (translateParameterSet localPoints v) (translateParameterSet localPoints w) ↔
        Disjoint ((translateParameterSet localPoints v) : Set (Point 3))
          ((translateParameterSet localPoints w) : Set (Point 3)) := by
      simp [Finset.disjoint_left, Set.disjoint_left]
    exact h_iff.mpr h_set_disj

  -- Cardinality equality
  have h_disj_for_card : ∀ (i : Point 3), i ∈ translations → ∀ (j : Point 3), j ∈ translations →
      i ≠ j → Disjoint (translateParameterSet localPoints i) (translateParameterSet localPoints j) :=
    translated_disjoint
  have amplified_card_eq :
      amplified.enncard = translations.enncard * localPoints.enncard := by
    have h1 : amplified.card = ∑ v ∈ translations, (translateParameterSet localPoints v).card := by
      rw [amplifieddef, amplifiedParameterSet, Finset.card_biUnion h_disj_for_card]
      <;> rfl
    have h2 : ∀ v ∈ translations, (translateParameterSet localPoints v).card = localPoints.card := by
      intro v _
      rw [translateParameterSet, Finset.card_image_of_injective _]
      <;> intro a b h <;> exact add_right_cancel h
    have h3 : amplified.card = translations.card * localPoints.card := by
      rw [h1, Finset.sum_congr rfl h2, Finset.sum_const]
      <;> ring
    have h4 : amplified.enncard = (amplified.card : ENNReal) := by rfl
    have h5 : translations.enncard * localPoints.enncard =
        ((translations.card : ENNReal) * (localPoints.card : ENNReal)) := by rfl
    rw [h4, h3, h5]
    <;> norm_cast

  -- Copy source
  have copy_source : ∀ v ∈ translations, ∀ p ∈ localPoints, p + v ∈ amplified := by
    intro v hv p hp
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

  -- Local KT gives upper bound on total cardinality
  have hcontain' : ∀ p ∈ localPoints, dist p localCenter ≤ blockScale := by
    intro p hp
    have h : dist p localCenter ≤ blockScale / 10 := hcontain p hp
    have h2 : blockScale / 10 ≤ blockScale := by linarith [hblock_pos]
    exact h.trans h2
  have hblock_le_one : blockScale ≤ 1 := by
    have h1 : blockScale ≤ 1 / 100 := by
      calc blockScale = (100 * blockScale) / 100 := by ring
        _ ≤ 1 / 100 := by gcongr
    linarith
  have local_card_upper :
      localPoints.enncard ≤
        100 * Kakeya.realRpowENN
          (blockScale / fineScale) ktExponent :=
    IsKatzTao_total_card hkt hfine_block hblock_le_one hcontain'

  -- Global Katz-Tao bound
  have amplified_katzTao : amplified.IsKatzTao fineScale 1 100000 := by
    rw [amplifieddef, translationsdef]
    exact amplifiedParameterSet_isKatzTao
      hfine hblock_pos hfine_block hkt_pos hkt_one
      h_pos h_gt_blockScale5 h_cube
      localCenter localPoints hcontain hkt local_card_upper
      indices v_of_k v_of_k_injective v_coord

  -- Amplified cardinality lower bound
  have amplified_card_lower :
      Kakeya.realRpowENN (blockScale / fineScale) s *
          Kakeya.realRpowENN blockScale (-1) ≤
        10000000000 * amplified.enncard := by
    rw [amplified_card_eq]
    have h1 : Kakeya.realRpowENN (blockScale / fineScale) s ≤ 100000 * localPoints.enncard := hcard
    have h2 : Kakeya.realRpowENN blockScale (-1) ≤ 100000 * translations.enncard :=
      translations_card_lower
    calc
      Kakeya.realRpowENN (blockScale / fineScale) s *
            Kakeya.realRpowENN blockScale (-1)
      _ ≤ (100000 * localPoints.enncard) * (100000 * translations.enncard) := by gcongr
      _ = 10000000000 * (translations.enncard * localPoints.enncard) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring

  exact ⟨
    translations,
    translations_nonempty,
    translations_card_lower,
    translations_card_upper,
    translated_disjoint,
    amplified,
    rfl,
    amplified_in_unitBall,
    amplified_half,
    amplified_katzTao,
    amplified_card_lower,
    amplified_card_eq,
    copy_source
  ⟩

end Kakeya.Assouad
