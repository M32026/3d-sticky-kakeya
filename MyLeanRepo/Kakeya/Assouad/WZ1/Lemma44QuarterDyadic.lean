import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44DyadicAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44SingleScaleBadPair
import MyLeanRepo.Kakeya.Assouad.WZ1.HeavyLinePacking

/-!
# WZ1 Quarter Thin Tubes - main dyadic assembly

Uses dune's Lemma44DyadicAssembly helpers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open scoped ENNReal

/-- Dyadic assembly for Regime 2: ζ < 1/4 AND 12α/ζ+4λ < 1.

Takes explicit arithmetic premise proofs so the main theorem can choose δ₀.
The scale family threshold is `2*T` where `T = δ^(12α/ζ+4λ)`, ensuring that
dyadic rounding of any `r ≤ T` lands in the family.
-/
lemma dyadic_assembly_main
    {delta lambda zeta alpha : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (hzeta_small : zeta < 1 / 4)
    (hE_small : 12 * alpha / zeta + 4 * lambda < 1)
    {G₁ G₂ : DiscreteSet 2}
    (hG1ne : G₁.Nonempty) (hG2ne : G₂.Nonempty)
    (hG1ball : G₁.IsInUnitBall) (hG2ball : G₂.IsInUnitBall)
    (hG1sep : G₁.IsDeltaSeparated delta) (hG2sep : G₂.IsDeltaSeparated delta)
    (hFrost1 : G₁.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (hFrost2 : G₂.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (hMutSep : WZ1MutuallySeparated G₁ G₂ (1 / 2))
    (hNonConc : WZ1LineNonConcentration delta lambda zeta G₂)
    -- Arithmetic premises quantified over all scales in the family
    (hK_ge_one : 1 ≤ Real.rpow delta (-3 * alpha / zeta - lambda) / Real.rpow 2 (1 / 4 : ℝ))
    (hscale1 : ∀ R ∈ dyadic_scale_family delta (2 * Real.rpow delta (12 * alpha / zeta + 4 * lambda)), R ≤ 1)
    (h13scale : ∀ R ∈ dyadic_scale_family delta (2 * Real.rpow delta (12 * alpha / zeta + 4 * lambda)), 13 * R ≤ 1)
    (hprem2 : ∀ R ∈ dyadic_scale_family delta (2 * Real.rpow delta (12 * alpha / zeta + 4 * lambda)),
      8 * (13 * R) ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta))
    (hprem3 :
      (312000 : ℝ) / (Real.rpow delta (-3 * alpha / zeta - lambda) / Real.rpow 2 (1 / 4 : ℝ)) ^ 4 *
        Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
      Real.rpow delta (4 * alpha))
    (h_absorb : (Real.sqrt 312002 * ((dyadic_scale_family delta (2 * Real.rpow delta (12 * alpha / zeta + 4 * lambda))).card : ℝ)) *
      Real.rpow delta (2 * alpha) ≤ Real.rpow delta alpha) :
    HasDiscreteThinTubes delta (1 / 4)
      (Real.rpow delta (-3 * alpha / zeta - lambda))
      (Real.rpow delta alpha) G₁ G₂ := by
  set E : ℝ := 12 * alpha / zeta + 4 * lambda with hE
  set T : ℝ := Real.rpow delta E with hT
  set T' : ℝ := 2 * T with hT'
  set K_final : ℝ := Real.rpow delta (-3 * alpha / zeta - lambda) with hK_final
  set K_int : ℝ := K_final / Real.rpow 2 (1 / 4 : ℝ) with hK_int
  have hE_pos : 0 < E := by positivity
  have hT_gt_delta : delta < T := by
    have hE_lt_one : E < 1 := hE_small
    have h : Real.rpow delta 1 < Real.rpow delta E :=
      Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 hE_lt_one
    have h' : Real.rpow delta 1 = delta := by simp
    rw [h'] at h
    exact h
  have hT'_gt_delta : delta < T' := by linarith
  have hT_pos : 0 < T := by
    rw [hT]
    exact Real.rpow_pos_of_pos hdelta E
  have h_exp_sum : (-3 * alpha / zeta - lambda) + (1 / 4 : ℝ) * E = 0 := by
    simp [hE] <;> field_simp [hzeta.ne'] <;> ring
  have h1 : Real.rpow T (1 / 4 : ℝ) = Real.rpow delta ((1 / 4 : ℝ) * E) := by
    rw [hT]
    have h_mul : Real.rpow (Real.rpow delta E) (1 / 4 : ℝ) = Real.rpow delta (E * (1 / 4 : ℝ)) :=
      (Real.rpow_mul hdelta.le E (1 / 4 : ℝ)).symm
    have h_comm : E * (1 / 4 : ℝ) = (1 / 4 : ℝ) * E := by ring
    rw [h_mul, h_comm]
  have hK_final_T : K_final * Real.rpow T (1 / 4 : ℝ) = 1 := by
    rw [h1]
    have h_rpow_add : Real.rpow delta (-3 * alpha / zeta - lambda) * Real.rpow delta ((1 / 4 : ℝ) * E) =
        Real.rpow delta ((-3 * alpha / zeta - lambda) + (1 / 4 : ℝ) * E) := by
      have h : Real.rpow delta ((-3 * alpha / zeta - lambda) + (1 / 4 : ℝ) * E) =
          Real.rpow delta (-3 * alpha / zeta - lambda) * Real.rpow delta ((1 / 4 : ℝ) * E) :=
        Real.rpow_add hdelta (-3 * alpha / zeta - lambda) ((1 / 4 : ℝ) * E)
      exact h.symm
    rw [hK_final, h_rpow_add, h_exp_sum]
    <;> simp
  let scales := dyadic_scale_family delta T'
  let bad : ℝ → Finset (Point2 × Point2) := fun R =>
    (G₁ ×ˢ G₂).filter fun pair => WZ1BadAtScale G₁ G₂ R K_int pair.1 pair.2
  have h_single_scale : ∀ R ∈ scales,
      ((bad R).card : ℝ) ≤ Real.sqrt 312002 * Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
    intro R hR
    have hR_pos : 0 < R := dyadic_scale_family.pos hdelta hT'_gt_delta hR
    have hR_ge_delta : delta ≤ R := by
      rcases Finset.mem_image.mp hR with ⟨k, _, rfl⟩
      have h : (1 : ℝ) ≤ (2 : ℝ)^k := by
        have h' : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
          intro n; induction n <;> simp [*, pow_succ] <;> linarith
        exact h' k
      nlinarith
    have hR_le_one : R ≤ 1 := hscale1 R hR
    have h13 : 13 * R ≤ 1 := h13scale R hR
    have hR_lt_T' : R < T' := dyadic_scale_family.all_lt_T hdelta hT'_gt_delta hR
    have hK_small : K_int * Real.rpow R (1 / 4 : ℝ) < 1 := by
      have h_pos1 : 0 ≤ R := by linarith
      have h_pos2 : 0 < T' := by positivity
      have h_rpow_lt : Real.rpow R (1 / 4 : ℝ) < Real.rpow T' (1 / 4 : ℝ) :=
        Real.rpow_lt_rpow h_pos1 hR_lt_T' (by norm_num)
      have hK_int_pos : 0 < K_int := by positivity
      have h : K_int * Real.rpow R (1 / 4 : ℝ) < K_int * Real.rpow T' (1 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left h_rpow_lt hK_int_pos
      have hT_pos' : 0 ≤ T := by exact hT_pos.le
      have h3 : Real.rpow T' (1 / 4 : ℝ) = Real.rpow 2 (1 / 4 : ℝ) * Real.rpow T (1 / 4 : ℝ) := by
        rw [hT']
        exact Real.mul_rpow (show (0 : ℝ) ≤ 2 from by norm_num) hT_pos'
      have h2 : K_int * Real.rpow T' (1 / 4 : ℝ) = 1 := by
        rw [h3, hK_int]
        have h5 : (K_final / Real.rpow 2 (1 / 4 : ℝ)) * (Real.rpow 2 (1 / 4 : ℝ) * Real.rpow T (1 / 4 : ℝ)) =
            K_final * Real.rpow T (1 / 4 : ℝ) := by
          field_simp <;> ring
        rw [h5, hK_final_T]
      rw [h2] at h
      exact h
    exact wz1_lemma44_single_scale_bad_pair wz1_heavy_line_packing
      delta lambda zeta alpha hdelta hdelta1 hlambda hzeta halpha
      G₁ G₂ hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2 hMutSep hNonConc
      K_int R hK_ge_one hR_pos hR_ge_delta hR_le_one hK_small h13 (hprem2 R hR) hprem3
  let bad_union : Finset (Point2 × Point2) := scales.biUnion bad
  have hbad_sub : bad_union ⊆ G₁ ×ˢ G₂ := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨R, _, hx2⟩
    exact Finset.mem_filter.mp hx2 |>.1
  have hbad_card : (bad_union.card : ℝ) ≤
      Real.rpow delta alpha * (G₁.card : ℝ) * (G₂.card : ℝ) := by
    have h1 := finite_bad_union_bound h_single_scale
    have h3 : (bad_union.card : ℝ) ≤
        (scales.card : ℝ) * (Real.sqrt 312002 * Real.rpow delta (2 * alpha)) * (G₁.card : ℝ) * (G₂.card : ℝ) := h1
    have h4 : (scales.card : ℝ) * (Real.sqrt 312002 * Real.rpow delta (2 * alpha)) * (G₁.card : ℝ) * (G₂.card : ℝ) =
        (Real.sqrt 312002 * (scales.card : ℝ)) * Real.rpow delta (2 * alpha) * (G₁.card : ℝ) * (G₂.card : ℝ) := by ring
    rw [h4] at h3
    have h5 : (Real.sqrt 312002 * (scales.card : ℝ)) * Real.rpow delta (2 * alpha) ≤ Real.rpow delta alpha := h_absorb
    have h6 : 0 ≤ (G₁.card : ℝ) * (G₂.card : ℝ) := by positivity
    nlinarith
  let E_good : Finset (Point2 × Point2) := (G₁ ×ˢ G₂) \ bad_union
  have hc0 : 0 ≤ Real.rpow delta alpha := Real.rpow_nonneg (by linarith) _
  have hc1 : Real.rpow delta alpha < 1 := by
    apply Real.rpow_lt_one <;> linarith
  have h_retention : (1 - ENNReal.ofReal (Real.rpow delta alpha)) * (G₁.card : ENNReal) * (G₂.card : ENNReal) ≤
      (E_good.card : ENNReal) :=
    complement_retention hc0 hc1.le hbad_sub hbad_card
  have h_not_bad_all : ∀ (b₁ : Point2), b₁ ∈ G₁ → ∀ (b₂ : Point2), b₂ ∈ G₂ →
      (b₁, b₂) ∈ E_good → ∀ R ∈ scales, ¬ WZ1BadAtScale G₁ G₂ R K_int b₁ b₂ := by
    intro b₁ hb₁ b₂ hb₂ hgood R hR
    have h_not_in_union : (b₁, b₂) ∉ bad_union := (Finset.mem_sdiff.mp hgood).2
    intro h_bad
    have h7 : (b₁, b₂) ∈ G₁ ×ˢ G₂ := (Finset.mem_sdiff.mp hgood).1
    have h8 : (b₁, b₂) ∈ bad R := Finset.mem_filter.mpr ⟨h7, h_bad⟩
    have h9 : (b₁, b₂) ∈ bad_union := Finset.mem_biUnion.mpr ⟨R, hR, h8⟩
    exact h_not_in_union h9
  have h_tube : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, delta ≤ r →
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_good).card : ENNReal) ≤
        ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * G₂.enncard := by
    intro b₁ hb₁ ℓ hb₁_line hfin r hr
    by_cases h_r_le_T : r ≤ T
    · -- Case r ≤ T: dyadic rounding
      rcases dyadic_rounding hdelta hr with ⟨k, h1, h2⟩
      let R : ℝ := delta * (2 : ℝ)^k
      have hR_lt_T' : R < T' := by
        dsimp only [R, T']
        have h : R < 2 * r := h2
        linarith
      have hR_in_scales : R ∈ scales := by
        dsimp only [scales, dyadic_scale_family]
        let N := Nat.ceil (Real.logb 2 (T' / delta))
        have h9 : (2 : ℝ)^k < T' / delta := by
          have h10 : delta * (2 : ℝ)^k < T' := hR_lt_T'
          have h11 : (2 : ℝ)^k < T' / delta := by
            calc (2 : ℝ)^k
              = (delta * (2 : ℝ)^k) / delta := by field_simp [hdelta.ne'] <;> ring
            _ < T' / delta := by gcongr
          exact h11
        have h12 : (k : ℝ) < Real.logb 2 (T' / delta) := by
          have h13 : Real.logb 2 ((2 : ℝ)^k) = (k : ℝ) := by
            simp [Real.logb_pow] <;> ring
          have h14 : Real.logb 2 ((2 : ℝ)^k) < Real.logb 2 (T' / delta) :=
            Real.logb_lt_logb (by norm_num) (by positivity) h9
          rw [h13] at h14
          exact h14
        have h_k_lt_N : k < N := by
          have h15 : (k : ℝ) < (N : ℝ) := by
            have h16 : Real.logb 2 (T' / delta) ≤ (N : ℝ) := Nat.le_ceil _
            linarith
          exact_mod_cast h15
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr h_k_lt_N, rfl⟩
      have h_not_bad_R : ∀ (x : Point2), x ∈ G₁ → ∀ (y : Point2), y ∈ G₂ →
          (x, y) ∈ E_good → ¬ WZ1BadAtScale G₁ G₂ R K_int x y :=
        fun x hx y hy hgood => h_not_bad_all x hx y hy hgood R hR_in_scales
      have h_r_le_R : r ≤ R := h1
      have h_bound := good_pair_tube_bound h_not_bad_R hb₁ ℓ hb₁_line hfin h_r_le_R
      have h_R_lt_2r : R < 2 * r := h2
      have hr_pos : 0 ≤ r := by linarith
      have hR_le_2r : R ≤ 2 * r := by linarith
      have h_K_int_bound : K_int * Real.rpow R (1 / 4 : ℝ) ≤ K_final * Real.rpow r (1 / 4 : ℝ) := by
        have hR_nonneg : 0 ≤ R := by linarith
        have h_rpow2 : Real.rpow R (1 / 4 : ℝ) ≤ Real.rpow (2 * r) (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hR_nonneg hR_le_2r (by norm_num)
        have h_mul : Real.rpow (2 * r) (1 / 4 : ℝ) = Real.rpow 2 (1 / 4 : ℝ) * Real.rpow r (1 / 4 : ℝ) :=
          Real.mul_rpow (show (0 : ℝ) ≤ 2 from by norm_num) hr_pos
        have h_rpow2_pos : 0 < Real.rpow 2 (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) (1 / 4 : ℝ)
        calc
          K_int * Real.rpow R (1 / 4 : ℝ)
            ≤ K_int * Real.rpow (2 * r) (1 / 4 : ℝ) := by exact mul_le_mul_of_nonneg_left h_rpow2 (by positivity)
          _ = K_int * (Real.rpow 2 (1 / 4 : ℝ) * Real.rpow r (1 / 4 : ℝ)) := by rw [h_mul]
          _ = (K_final / Real.rpow 2 (1 / 4 : ℝ)) * (Real.rpow 2 (1 / 4 : ℝ) * Real.rpow r (1 / 4 : ℝ)) := by rw [hK_int]
          _ = K_final * Real.rpow r (1 / 4 : ℝ) := by
            field_simp [h_rpow2_pos.ne'] <;> ring
      have h_ennreal : ENNReal.ofReal (K_int * Real.rpow R (1 / 4 : ℝ)) ≤
          ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_K_int_bound
      calc
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_good).card : ENNReal)
          ≤ ENNReal.ofReal (K_int * Real.rpow R (1 / 4 : ℝ)) * G₂.enncard := h_bound
        _ ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * G₂.enncard := by
          gcongr
    · -- Case r > T: trivial bound
      have h3 : T < r := by linarith
      have h4 : Real.rpow T (1 / 4 : ℝ) < Real.rpow r (1 / 4 : ℝ) :=
        Real.rpow_lt_rpow (by positivity) h3 (by norm_num)
      have h5 : K_final * Real.rpow T (1 / 4 : ℝ) = 1 := hK_final_T
      have hK_pos : 0 < K_final := by
        have h : 0 < Real.rpow delta (-3 * alpha / zeta - lambda) := Real.rpow_pos_of_pos hdelta _
        exact h
      have hK_final_r : 1 < K_final * Real.rpow r (1 / 4 : ℝ) := by
        have h : K_final * Real.rpow T (1 / 4 : ℝ) < K_final * Real.rpow r (1 / 4 : ℝ) :=
          mul_lt_mul_of_pos_left h4 hK_pos
        rw [h5] at h
        exact h
      have h_filter_sub : (G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_good) ⊆ G₂ :=
        Finset.filter_subset _ _
      let S_filt := G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E_good
      have h61 : S_filt.card ≤ G₂.card := Finset.card_le_card h_filter_sub
      have h6 : (S_filt.card : ENNReal) ≤ G₂.enncard := by
        have h62 : (S_filt.card : ENNReal) ≤ (G₂.card : ENNReal) := by exact_mod_cast h61
        have h63 : (G₂.card : ENNReal) = G₂.enncard := by
          simp [DiscreteSet.enncard]
        rw [h63] at h62
        exact h62
      have h7 : (1 : ENNReal) ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) := by
        have h71 : (1 : ℝ) ≤ K_final * Real.rpow r (1 / 4 : ℝ) := hK_final_r.le
        have h72 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
        rw [h72]
        exact ENNReal.ofReal_le_ofReal h71
      have h9 : G₂.enncard ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * G₂.enncard := by
        have h10 : (1 : ENNReal) * G₂.enncard ≤ ENNReal.ofReal (K_final * Real.rpow r (1 / 4 : ℝ)) * G₂.enncard := by
          gcongr
        simpa using h10
      exact h6.trans h9
  have hK_final_gt_one : 1 < K_final := by
    have h_exp_neg : -3 * alpha / zeta - lambda < 0 := by
      have h1 : 0 < 3 * alpha / zeta := by positivity
      linarith
    have h : Real.rpow delta (-3 * alpha / zeta - lambda) > 1 :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg hdelta hdelta1 h_exp_neg
    simpa [hK_final] using h
  have h_alpha_pos : 0 < Real.rpow delta alpha := Real.rpow_pos_of_pos hdelta alpha
  have h_alpha_lt_one : Real.rpow delta alpha < 1 := hc1
  exact ⟨by norm_num, by linarith, ⟨by linarith, by linarith⟩,
    E_good, by simp [E_good], h_retention, h_tube⟩

end Kakeya.Assouad
