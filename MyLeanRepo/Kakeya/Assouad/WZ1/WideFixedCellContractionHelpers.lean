import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Contraction helpers for fixed-cell normalization

Transports line nonconcentration under an affine map `x ↦ s • x + t`
where the separation scale contracts from `delta` to `m * delta` with
`0 < m ≤ s`.  The nonconcentration exponent strengthens from
`3 * lambda / 4` to `lambda`, paid for by the contraction factor.

The key smallness condition is `delta ^ (lambda / 4) ≤ m ^ (1 - lambda)`.
-/

namespace Kakeya.Assouad

open scoped ENNReal

lemma WZ1LineNonConcentration.contraction
    {delta lambda zeta s m : ℝ} {G : DiscreteSet 2} {trans : Point2}
    (h : WZ1LineNonConcentration delta (3 * lambda / 4) zeta G)
    (hs_pos : 0 < s) (hm_pos : 0 < m) (hm_le_s : m ≤ s)
    (hlambda_pos : 0 < lambda) (hlambda_le_one : lambda ≤ 1)
    (hzeta : 0 ≤ zeta) (hdelta : 0 < delta)
    (hsmall : delta ^ (lambda / 4) ≤ m ^ (1 - lambda)) :
    WZ1LineNonConcentration (m * delta) lambda zeta
      (G.image (fun x => s • x + trans)) := by
  let G' : DiscreteSet 2 := G.image (fun x : Point2 => s • x + trans)
  let f : Point2 → Point2 := fun x => s • x + trans
  have h_inj : Function.Injective f := by
    intro x y h
    have h2 : s • x + trans = s • y + trans := h
    have h3 : s • x = s • y := by simpa using h2
    have h9 : s ≠ 0 := hs_pos.ne'
    have h10 : s⁻¹ • (s • x) = s⁻¹ • (s • y) := congr_arg (fun v : Point2 => s⁻¹ • v) h3
    simpa [h9, smul_smul] using h10
  have h_card : G'.card = G.card :=
    Finset.card_image_of_injective _ h_inj
  have h_enncard : G'.enncard = G.enncard := by
    simp [DiscreteSet.enncard, h_card]
  intro normal hnormal level r hdelta' hrone
  set r'' : ℝ := r / s with hr''_def
  set level' : ℝ := (level - inner ℝ trans normal) / s with hlevel'_def
  let p' : Point2 → Prop := fun y => |inner ℝ y normal - level| ≤ r
  let p : Point2 → Prop := fun x => |inner ℝ x normal - level'| ≤ r''
  have h_iff : ∀ (x : Point2), p' (f x) ↔ p x := by
    intro x
    dsimp only [p', p]
    have h_inner : inner ℝ (f x) normal = s * inner ℝ x normal + inner ℝ trans normal := by
      have h1 : inner ℝ (f x) normal = inner ℝ (s • x) normal + inner ℝ trans normal := by
        rw [inner_add_left]
      rw [h1]
      have h2 : inner ℝ (s • x) normal = s * inner ℝ x normal := by
        rw [inner_smul_left]; simp
      rw [h2]
    have h_level' : s * level' = level - inner ℝ trans normal := by
      rw [hlevel'_def]
      field_simp [hs_pos.ne']
    have h_eq : inner ℝ (f x) normal - level = s * (inner ℝ x normal - level') := by
      rw [h_inner]
      linarith [h_level']
    have h_abs : |inner ℝ (f x) normal - level| = s * |inner ℝ x normal - level'| := by
      rw [h_eq, abs_mul, abs_of_pos hs_pos]
    rw [h_abs]
    have h_equiv : s * |inner ℝ x normal - level'| ≤ r ↔ |inner ℝ x normal - level'| ≤ r / s := by
      constructor
      · intro h4
        calc |inner ℝ x normal - level'|
          = (s * |inner ℝ x normal - level'|) / s := by field_simp [hs_pos.ne']
        _ ≤ r / s := by gcongr
      · intro h4
        calc s * |inner ℝ x normal - level'|
          ≤ s * (r / s) := by gcongr
        _ = r := by field_simp [hs_pos.ne']
    simpa [hr''_def] using h_equiv
  have h_filter : G'.filter p' = (G.filter p).image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hyG', hp'⟩
      rcases Finset.mem_image.mp hyG' with ⟨x, hxG, rfl⟩
      have hpx : p x := (h_iff x).mp hp'
      exact ⟨x, ⟨hxG, hpx⟩, rfl⟩
    · rintro ⟨x, ⟨hxG, hp⟩, rfl⟩
      have hp' : p' (f x) := (h_iff x).mpr hp
      exact ⟨Finset.mem_image.mpr ⟨x, hxG, rfl⟩, hp'⟩
  have h_card_eq : (G'.filter p').card = (G.filter p).card := by
    rw [h_filter]
    exact Finset.card_image_of_injective _ h_inj
  have h_rpos : 0 < r := by
    have h : 0 < m * delta := by positivity
    linarith [hdelta']
  have h_r''pos : 0 < r'' := by
    dsimp only [r'']
    exact div_pos h_rpos hs_pos

  -- If m * delta > 1, the hypotheses m*delta ≤ r ≤ 1 are contradictory.
  by_cases hmd : m * delta ≤ 1
  · -- Main case: m * delta ≤ 1
    have hdelta_le_one : delta ≤ 1 := by
      by_contra h'
      have hdelta_gt_one : 1 < delta := by linarith
      have h1 : 1 < delta ^ (lambda / 4) :=
        Real.one_lt_rpow hdelta_gt_one (by linarith)
      have h2 : 1 < m ^ (1 - lambda) := by linarith [hsmall]
      by_cases hlam : lambda < 1
      · have h3 : 1 < m := by
          by_contra h4
          have h5 : m ≤ 1 := by linarith
          have h6 : m ^ (1 - lambda) ≤ 1 := by
            apply Real.rpow_le_one
            · linarith
            · linarith
            · linarith
          linarith
        have h7 : 1 < m * delta := by
          have h71 : 0 < m := by linarith
          nlinarith
        linarith
      · have hlam' : lambda = 1 := by linarith
        rw [hlam'] at h2
        norm_num at h2 <;> linarith

    -- Key algebraic identity: m * m^(-lambda) = m^(1 - lambda)
    have h_m_id : m * m ^ (-lambda) = m ^ (1 - lambda) := by
      have h_add : m ^ (1 - lambda) = m ^ (1 : ℝ) * m ^ (-lambda) := by
        rw [← Real.rpow_add hm_pos] <;> ring
      simpa using h_add.symm

    -- Key inequality: delta^(lambda/4) ≤ s * m^(-lambda)
    have h_key1 : delta ^ (lambda / 4) ≤ s * m ^ (-lambda) := by
      have h1 : m ^ (1 - lambda) ≤ s * m ^ (-lambda) := by
        rw [← h_m_id]
        have h2 : m * m ^ (-lambda) ≤ s * m ^ (-lambda) := by
          gcongr
          <;> positivity
        exact h2
      exact hsmall.trans h1

    by_cases hcase : r'' ≤ 1
    · -- Case A: r/s ≤ 1
      by_cases hcase2 : delta ≤ r''
      · -- Subcase A1: delta ≤ r/s ≤ 1, apply h at r''
        have h_main := h normal hnormal level' r'' hcase2 hcase
        have h_ineq : delta ^ (-(3 * lambda / 4)) * r'' ≤ (m * delta) ^ (-lambda) * r := by
          have h9 : r'' = r / s := by rfl
          rw [h9]
          have h10 : delta ^ (-(3 * lambda / 4)) * (r / s) =
              (delta ^ (-(3 * lambda / 4)) / s) * r := by ring
          rw [h10]
          have h11 : delta ^ (-(3 * lambda / 4)) / s ≤ (m * delta) ^ (-lambda) := by
            have h12 : delta ^ (lambda / 4) ≤ s * m ^ (-lambda) := h_key1
            have h13 : delta ^ (-(3 * lambda / 4)) = delta ^ (-lambda) * delta ^ (lambda / 4) := by
              rw [← Real.rpow_add hdelta] <;> ring
            have h14 : (m * delta) ^ (-lambda) = m ^ (-lambda) * delta ^ (-lambda) := by
              rw [Real.mul_rpow (by linarith) (by linarith)]
            rw [h13, h14]
            have h15 : 0 < delta ^ (-lambda) := Real.rpow_pos_of_pos hdelta _
            calc
              (delta ^ (-lambda) * delta ^ (lambda / 4)) / s
                = delta ^ (-lambda) * (delta ^ (lambda / 4) / s) := by ring
              _ ≤ delta ^ (-lambda) * (m ^ (-lambda)) := by
                gcongr
                have h16 : delta ^ (lambda / 4) / s ≤ m ^ (-lambda) := by
                  calc delta ^ (lambda / 4) / s
                    ≤ (s * m ^ (-lambda)) / s := by gcongr
                    _ = m ^ (-lambda) := by
                      field_simp [hs_pos.ne'] <;> ring
                exact h16
              _ = m ^ (-lambda) * delta ^ (-lambda) := by ring
          have h17 : 0 ≤ r := by linarith
          gcongr
        have h_bases_nonneg : 0 ≤ delta ^ (-(3 * lambda / 4)) * r'' := by positivity
        have h_rpow_mono : Kakeya.realRpowENN (delta ^ (-(3 * lambda / 4)) * r'') zeta ≤
            Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta := by
          simp only [Kakeya.realRpowENN]
          apply ENNReal.ofReal_le_ofReal
          exact Real.rpow_le_rpow h_bases_nonneg h_ineq hzeta
        calc
          ((G'.filter p').card : ENNReal)
              = ((G.filter p).card : ENNReal) := by exact_mod_cast h_card_eq
          _ ≤ Kakeya.realRpowENN (delta ^ (-(3 * lambda / 4)) * r'') zeta * G.enncard := h_main
          _ ≤ Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta * G.enncard := by
              gcongr
          _ = Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta * G'.enncard := by
              rw [h_enncard]
      · -- Subcase A2: r/s < delta, enlarge to radius delta
        have h_lt : r'' < delta := by linarith
        let p_delta : Point2 → Prop := fun x => |inner ℝ x normal - level'| ≤ delta
        have h_subset : G.filter p ⊆ G.filter p_delta := by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          have hpx : p x := hx.2
          have hpx2 : p_delta x := by
            dsimp only [p, p_delta] at hpx ⊢
            calc |inner ℝ x normal - level'| ≤ r'' := hpx
              _ ≤ delta := by linarith
          exact ⟨hx.1, hpx2⟩
        have h_card_le : (G.filter p).card ≤ (G.filter p_delta).card :=
          Finset.card_le_card h_subset
        have h_main := h normal hnormal level' delta (by linarith) hdelta_le_one
        have h_ineq : delta ^ (-(3 * lambda / 4)) * delta ≤ (m * delta) ^ (-lambda) * r := by
          have h1 : delta ^ (-(3 * lambda / 4)) * delta = delta ^ (1 - 3 * lambda / 4) := by
            calc
              delta ^ (-(3 * lambda / 4)) * delta
                = delta ^ (-(3 * lambda / 4)) * delta ^ (1 : ℝ) := by simp
              _ = delta ^ (-(3 * lambda / 4) + 1) := by rw [← Real.rpow_add hdelta] <;> ring
              _ = delta ^ (1 - 3 * lambda / 4) := by rw [show (-(3 * lambda / 4) + 1) = (1 - 3 * lambda / 4) by ring]
          rw [h1]
          have h4 : (m * delta) ^ (1 - lambda) ≤ (m * delta) ^ (-lambda) * r := by
            have h5 : (m * delta) ^ (-lambda) * r ≥ (m * delta) ^ (-lambda) * (m * delta) := by
              gcongr
              <;> linarith
            have hpos2 : 0 < m * delta := by positivity
            have h6 : (m * delta) ^ (-lambda) * (m * delta) = (m * delta) ^ (1 - lambda) := by
              calc
                (m * delta) ^ (-lambda) * (m * delta)
                  = (m * delta) ^ (-lambda) * (m * delta) ^ (1 : ℝ) := by simp
                _ = (m * delta) ^ (-lambda + 1) := by rw [← Real.rpow_add hpos2] <;> ring
                _ = (m * delta) ^ (1 - lambda) := by rw [show (-lambda + 1) = (1 - lambda) by ring]
            linarith
          have h7 : delta ^ (1 - 3 * lambda / 4) ≤ (m * delta) ^ (1 - lambda) := by
            have h8 : (m * delta) ^ (1 - lambda) = m ^ (1 - lambda) * delta ^ (1 - lambda) := by
              rw [Real.mul_rpow (by linarith) (by linarith)]
            rw [h8]
            have h9 : delta ^ (1 - 3 * lambda / 4) = delta ^ (lambda / 4) * delta ^ (1 - lambda) := by
              have h10 : delta ^ (lambda / 4) * delta ^ (1 - lambda) = delta ^ (lambda / 4 + (1 - lambda)) := by
                rw [← Real.rpow_add hdelta] <;> ring
              have h11 : lambda / 4 + (1 - lambda) = 1 - 3 * lambda / 4 := by ring
              rw [h10, h11]
            rw [h9]
            have h12 : 0 ≤ delta ^ (1 - lambda) := by positivity
            nlinarith [hsmall]
          linarith
        have h_bases_nonneg : 0 ≤ delta ^ (-(3 * lambda / 4)) * delta := by positivity
        have h_rpow_mono : Kakeya.realRpowENN (delta ^ (-(3 * lambda / 4)) * delta) zeta ≤
            Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta := by
          simp only [Kakeya.realRpowENN]
          apply ENNReal.ofReal_le_ofReal
          exact Real.rpow_le_rpow h_bases_nonneg h_ineq hzeta
        calc
          ((G'.filter p').card : ENNReal)
              = ((G.filter p).card : ENNReal) := by exact_mod_cast h_card_eq
          _ ≤ ((G.filter p_delta).card : ENNReal) := by exact_mod_cast h_card_le
          _ ≤ Kakeya.realRpowENN (delta ^ (-(3 * lambda / 4)) * delta) zeta * G.enncard := h_main
          _ ≤ Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta * G.enncard := by
              gcongr
          _ = Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta * G'.enncard := by
              rw [h_enncard]
    · -- Case B: r/s > 1, trivial bound using total cardinality
      have h_rs_gt_one : 1 < r'' := by linarith
      have h_r_gt_s : s < r := by
        dsimp only [r''] at h_rs_gt_one
        have h1 : 1 < r / s := h_rs_gt_one
        calc s
          = s * 1 := by ring
        _ < s * (r / s) := mul_lt_mul_of_pos_left h1 hs_pos
        _ = r := by field_simp [hs_pos.ne'] <;> ring
      have h_r_gt_m : m < r := by linarith
      have h_base_gt_one : 1 < (m * delta) ^ (-lambda) * r := by
        have h1 : (m * delta) ^ (-lambda) * r > (m * delta) ^ (-lambda) * m := by
          gcongr <;> linarith
        have h2 : (m * delta) ^ (-lambda) * m = m ^ (1 - lambda) * delta ^ (-lambda) := by
          have h3 : (m * delta) ^ (-lambda) = m ^ (-lambda) * delta ^ (-lambda) := by
            rw [Real.mul_rpow (by linarith) (by linarith)]
          have h4 : m ^ (-lambda) * m = m ^ (1 - lambda) := by
            calc
              m ^ (-lambda) * m
                = m ^ (-lambda) * m ^ (1 : ℝ) := by simp
              _ = m ^ (-lambda + 1) := by rw [← Real.rpow_add hm_pos] <;> ring
              _ = m ^ (1 - lambda) := by rw [show (-lambda + 1) = (1 - lambda) by ring]
          calc
            (m * delta) ^ (-lambda) * m
              = (m ^ (-lambda) * delta ^ (-lambda)) * m := by rw [h3]
            _ = (m ^ (-lambda) * m) * delta ^ (-lambda) := by ring
            _ = m ^ (1 - lambda) * delta ^ (-lambda) := by rw [h4]
        rw [h2] at h1
        have h4 : m ^ (1 - lambda) * delta ^ (-lambda) ≥ delta ^ (lambda / 4) * delta ^ (-lambda) := by
          gcongr <;> linarith [hsmall]
        have h5 : delta ^ (lambda / 4) * delta ^ (-lambda) = delta ^ (-3 * lambda / 4) := by
          have h6 : delta ^ (lambda / 4) * delta ^ (-lambda) = delta ^ (lambda / 4 + (-lambda)) := by
            rw [← Real.rpow_add hdelta] <;> ring
          have h7 : lambda / 4 + (-lambda) = -3 * lambda / 4 := by ring
          rw [h6, h7]
        rw [h5] at h4
        have h8 : 1 ≤ delta ^ (-3 * lambda / 4) := by
          have h9 : -3 * lambda / 4 ≤ 0 := by linarith
          have h10 : delta ^ (-3 * lambda / 4) ≥ delta ^ (0 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_ge
            <;> linarith
          simpa using h10
        linarith
      have h9 : 1 ≤ (m * delta) ^ (-lambda) * r := by linarith
      have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta := by
        simp only [Kakeya.realRpowENN]
        have h11 : (1 : ℝ) ≤ Real.rpow ((m * delta) ^ (-lambda) * r) zeta := by
          have h12 : Real.rpow (1 : ℝ) zeta ≤ Real.rpow ((m * delta) ^ (-lambda) * r) zeta := by
            apply Real.rpow_le_rpow
            · positivity
            · linarith
            · exact hzeta
          have h13 : Real.rpow (1 : ℝ) zeta = 1 := Real.one_rpow zeta
          rw [h13] at h12
          exact h12
        have h14 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
        have h15 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow ((m * delta) ^ (-lambda) * r) zeta) :=
          ENNReal.ofReal_le_ofReal h11
        rw [h14] at h15
        exact h15
      have h13 : ((G'.filter p').card : ENNReal) ≤ G'.enncard := by
        have h14 : (G'.filter p').card ≤ G'.card := Finset.card_le_card (Finset.filter_subset _ _)
        have h15 : G'.enncard = (G'.card : ENNReal) := by simp [DiscreteSet.enncard]
        rw [h15]
        exact_mod_cast h14
      calc
        ((G'.filter p').card : ENNReal)
          ≤ G'.enncard := h13
        _ = (1 : ENNReal) * G'.enncard := by simp
        _ ≤ Kakeya.realRpowENN ((m * delta) ^ (-lambda) * r) zeta * G'.enncard := by
          gcongr
  · -- Case m * delta > 1: contradictory hypotheses
    have h_contra : m * delta ≤ r := hdelta'
    have h_contra2 : r ≤ 1 := hrone
    linarith

end Kakeya.Assouad
