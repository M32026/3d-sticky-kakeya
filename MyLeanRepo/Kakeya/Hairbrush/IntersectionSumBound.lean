import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound.DirectionBand

/-!
# Intersection sum bound for 2D Kakeya

Dyadic angle decomposition: ∑_{U ≠ T} |Y(T) ∩ Y(U)| ≤ C * V * log(1/δ)

Submodules:
- `Preparations`: basic definitions, geometric bounds, ONB extraction
- `DirectionBand`: direction band containment and convex set construction
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Hairbrush

variable {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}

local instance : DecidableEq (Kakeya.DeltaTube δ) := Classical.decEq _

lemma direction_band_count
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {n : Point3} {C0 C_KT : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h_plane : LiesInTwoPlaneNeighborhood F n C0)
    (hKT : Kakeya.KatzTaoConvexWolffBound F C_KT)
    (hC0 : 0 ≤ C0) (hCKT : 0 ≤ C_KT)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ F)
    (S : Finset (Kakeya.DeltaTube δ))
    (hS : S ⊆ F.erase T)
    (h_inter : ∀ U ∈ S, (T.carrier ∩ U.carrier).Nonempty)
    {σ : ℝ} (hσ1 : 0 ≤ σ) (hσ2 : 2 * σ ≤ Real.pi / 2) :
    (S.filter (fun U => effectiveAngle T U ≤ 2 * σ)).card ≤
      ENNReal.ofReal (2000 * (C0 + 1) * C_KT * max 1 (σ / δ)) := by
  classical
  have hn_unit : ‖n‖ = 1 := h_plane.1
  have h_dir_plane : ∀ U ∈ F, |inner ℝ U.direction n| ≤ C0 * δ := h_plane.2
  have h_plane_T : |inner ℝ T.direction n| ≤ C0 * δ := h_dir_plane T hT
  rcases direction_band_geometric hδ hδ1 T n hn_unit C0 σ hC0 hσ1 hσ2 h_plane_T
    with ⟨W, hW_conv, hW_cont, hW_vol⟩
  let S_band := S.filter (fun U => effectiveAngle T U ≤ 2 * σ)
  have h_containment : ∀ U ∈ S_band, U.carrier ⊆ W := by
    intro U hU
    have hU_in_S : U ∈ S := (Finset.mem_filter.mp hU).1
    have hU_in_F : U ∈ F := by
      have h1 : U ∈ F.erase T := hS hU_in_S
      exact Finset.mem_of_mem_erase h1
    have h_angle : effectiveAngle T U ≤ 2 * σ := (Finset.mem_filter.mp hU).2
    have h_inter' : (T.carrier ∩ U.carrier).Nonempty := h_inter U hU_in_S
    have h_plane_U : |inner ℝ U.direction n| ≤ C0 * δ := h_dir_plane U hU_in_F
    exact hW_cont U h_plane_U h_angle h_inter'
  have h_filter_sub : S_band ⊆ F.filter (fun U => U.carrier ⊆ W) := by
    intro U hU
    have hU_in_F : U ∈ F := by
      have h1 : U ∈ S := (Finset.mem_filter.mp hU).1
      have h2 : U ∈ F.erase T := hS h1
      exact Finset.mem_of_mem_erase h2
    simp only [Finset.mem_filter]
    exact ⟨hU_in_F, h_containment U hU⟩
  have h_count : (S_band.card : ENNReal) ≤ F.containedCount W := by
    have h' : S_band ⊆ F.filter (fun U => U.carrier ⊆ W) := h_filter_sub
    have h'' : (S_band.card : ENNReal) ≤ ((F.filter (fun U => U.carrier ⊆ W)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h'
    simpa [Kakeya.TubeFamily.containedCount] using h''
  have hKT' := hKT W hW_conv
  have h_lower : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    Kakeya.Assouad.canonical_volume_lower hδ
  have hpos1 : 0 ≤ 2000 * (C0 + 1) * C_KT := by positivity
  have hpos2 : 0 ≤ 2000 * (C0 + 1) * max σ δ * δ := by positivity
  have h_inv : (Kakeya.deltaTubeVolume δ)⁻¹ ≤ (ENNReal.ofReal (δ ^ 2))⁻¹ := by
    exact ENNReal.inv_le_inv.mpr h_lower
  have h_mul : ENNReal.ofReal C_KT * MeasureTheory.volume W * (Kakeya.deltaTubeVolume δ)⁻¹ ≤
      ENNReal.ofReal C_KT * ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) * (ENNReal.ofReal (δ ^ 2))⁻¹ := by
    gcongr
    <;> assumption
  have h10 : max σ δ * δ / δ ^ 2 = max 1 (σ / δ) := by
    by_cases h : σ ≥ δ
    · rw [max_eq_left h]
      have h11 : σ / δ ≥ 1 := by
        have h12 : 0 < δ := hδ
        calc σ / δ ≥ δ / δ := by gcongr
          _ = 1 := by field_simp [h12.ne']
      rw [max_eq_right h11] <;> field_simp [hδ.ne'] <;> ring
    · have h' : σ < δ := by linarith
      rw [max_eq_right (by linarith)]
      have h11 : σ / δ < 1 := by
        have h12 : 0 < δ := hδ
        calc σ / δ < δ / δ := by gcongr
          _ = 1 := by field_simp [h12.ne']
      rw [max_eq_left (by linarith)] <;> field_simp [hδ.ne'] <;> ring
  have h_real_eq : (C_KT * (2000 * (C0 + 1) * max σ δ * δ)) * (δ ^ 2)⁻¹ = 2000 * (C0 + 1) * C_KT * max 1 (σ / δ) := by
    have h9 : (C_KT * (2000 * (C0 + 1) * max σ δ * δ)) * (δ ^ 2)⁻¹ = 2000 * (C0 + 1) * C_KT * (max σ δ * δ / δ ^ 2) := by
      field_simp [hδ.ne'] <;> ring
    rw [h9, h10] <;> ring
  have h_final_eq : ENNReal.ofReal C_KT * ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) * (ENNReal.ofReal (δ ^ 2))⁻¹ =
      ENNReal.ofReal (2000 * (C0 + 1) * C_KT * max 1 (σ / δ)) := by
    have hpos3 : 0 < δ ^ 2 := by positivity
    have h5 : (ENNReal.ofReal (δ ^ 2))⁻¹ = ENNReal.ofReal ((δ ^ 2)⁻¹) := by
      exact (ENNReal.ofReal_inv_of_pos hpos3).symm
    have h6 : ENNReal.ofReal C_KT * ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) * ENNReal.ofReal ((δ ^ 2)⁻¹) =
        ENNReal.ofReal ((C_KT * (2000 * (C0 + 1) * max σ δ * δ)) * (δ ^ 2)⁻¹) := by
      rw [←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h5, h6, h_real_eq]
  calc
    (S_band.card : ENNReal)
      ≤ F.containedCount W := h_count
    _ ≤ ENNReal.ofReal C_KT * MeasureTheory.volume W * (Kakeya.deltaTubeVolume δ)⁻¹ := hKT'
    _ ≤ ENNReal.ofReal C_KT * ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) * (ENNReal.ofReal (δ ^ 2))⁻¹ := h_mul
    _ = ENNReal.ofReal (2000 * (C0 + 1) * C_KT * max 1 (σ / δ)) := h_final_eq


-- ============================================================================
-- Sorry 3: Dyadic summation (PROVED)
-- ============================================================================

/-- Numeric constant bound: 1 + 24π + 4π√2 ≤ 32π. -/
lemma kakeya_log_constant : 1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2 ≤ 32 * Real.pi := by
  have h1 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff] <;> norm_num
  have h2 : 4 * Real.pi * Real.sqrt 2 ≤ 6 * Real.pi := by
    have hpos : 0 ≤ 4 * Real.pi := by positivity
    have h : 4 * Real.pi * Real.sqrt 2 ≤ 4 * Real.pi * (3 / 2) := mul_le_mul_of_nonneg_left h1 hpos
    have h' : 4 * Real.pi * (3 / 2) = 6 * Real.pi := by ring
    rw [h'] at h
    exact h
  have h3 : 1 ≤ 2 * Real.pi := by
    have h4 : 3 < Real.pi := Real.pi_gt_three
    linarith
  have h42 : 1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2 ≤ 1 + 30 * Real.pi := by
    calc 1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2
      = 1 + (24 * Real.pi + 4 * Real.pi * Real.sqrt 2) := by ring
    _ ≤ 1 + (24 * Real.pi + 6 * Real.pi) := by gcongr
    _ = 1 + 30 * Real.pi := by ring
  have h43 : 1 + 30 * Real.pi ≤ 32 * Real.pi := by
    have h44 : 1 ≤ 2 * Real.pi := h3
    linarith
  calc 1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2
    ≤ 1 + 30 * Real.pi := h42
  _ ≤ 32 * Real.pi := h43

/-- ENNReal multiplication bound for the final log constant comparison. -/
lemma enoreal_final_bound (C_pack : ℝ) (hC_nonneg : 0 ≤ C_pack) (V : ENNReal) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000) :
    ENNReal.ofReal C_pack * V *
      ENNReal.ofReal ((1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) ≤
    ENNReal.ofReal (C_pack * 32 * Real.pi) * V *
      ENNReal.ofReal (Real.log (1 / δ)) := by
  set A : ℝ := 1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2 with hA_def
  have hA_nonneg : 0 ≤ A := by positivity
  have h_igt : 1 < 1 / δ := by
    have h2 : δ < 1 := by linarith
    exact one_lt_one_div hδ h2
  have hlog_nonneg : 0 ≤ Real.log (1 / δ) := (Real.log_pos h_igt).le
  have h_const : A ≤ 32 * Real.pi := kakeya_log_constant
  let p : ℝ := C_pack
  let q : ℝ := A * Real.log (1 / δ)
  let r : ℝ := C_pack * 32 * Real.pi
  let s : ℝ := Real.log (1 / δ)
  have hq_nonneg : 0 ≤ q := by positivity
  have hr_nonneg : 0 ≤ r := by positivity
  have h_real : p * q ≤ r * s := by
    have h1 : p * A ≤ p * (32 * Real.pi) := mul_le_mul_of_nonneg_left h_const hC_nonneg
    have h2 : p * (32 * Real.pi) = r := by ring
    have h3 : p * q = (p * A) * s := by
      simp [p, q, s] <;> ring
    have h4 : r * s = (p * (32 * Real.pi)) * s := by
      have h41 : r = p * (32 * Real.pi) := h2.symm
      rw [h41]
      <;> rfl
    rw [h3, h4]
    exact mul_le_mul_of_nonneg_right h1 hlog_nonneg
  have h_left : ENNReal.ofReal p * ENNReal.ofReal q = ENNReal.ofReal (p * q) :=
    (ENNReal.ofReal_mul hC_nonneg).symm
  have h_right : ENNReal.ofReal r * ENNReal.ofReal s = ENNReal.ofReal (r * s) :=
    (ENNReal.ofReal_mul hr_nonneg).symm
  have h_inner : ENNReal.ofReal p * ENNReal.ofReal q ≤ ENNReal.ofReal r * ENNReal.ofReal s := by
    rw [h_left, h_right]
    exact ENNReal.ofReal_le_ofReal h_real
  set a : ENNReal := ENNReal.ofReal p with ha
  set b : ENNReal := ENNReal.ofReal q with hb
  set c : ENNReal := ENNReal.ofReal r with hc
  set d : ENNReal := ENNReal.ofReal s with hd
  have h_inner' : a * b ≤ c * d := h_inner
  have h_comm1 : a * V * b = V * (a * b) := by
    calc a * V * b
      = a * (V * b) := mul_assoc a V b
    _ = a * (b * V) := by rw [mul_comm V b]
    _ = (a * b) * V := by exact (mul_assoc a b V).symm
    _ = V * (a * b) := mul_comm (a * b) V
  have h_comm2 : c * V * d = V * (c * d) := by
    calc c * V * d
      = c * (V * d) := mul_assoc c V d
    _ = c * (d * V) := by rw [mul_comm V d]
    _ = (c * d) * V := by exact (mul_assoc c d V).symm
    _ = V * (c * d) := mul_comm (c * d) V
  rw [h_comm1, h_comm2]
  exact mul_le_mul_of_nonneg_left h_inner' (by positivity)

lemma dyadic_sum_bound
    {α : Type*} [DecidableEq α] {S : Finset α}
    (θ : α → ℝ) (vol : α → ENNReal)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (hθ1 : ∀ x ∈ S, 0 ≤ θ x)
    (hθ2 : ∀ x ∈ S, θ x ≤ Real.pi / 2)
    (C_pack : ℝ) (hC_nonneg : 0 ≤ C_pack)
    (h_count : ∀ σ : ℝ, 0 ≤ σ → 2 * σ ≤ Real.pi / 2 →
      (S.filter (fun x => θ x ≤ 2 * σ)).card ≤ ENNReal.ofReal (C_pack * max 1 (σ / δ)))
    (V : ENNReal) (hV_lower : ENNReal.ofReal (δ ^ 2) ≤ V)
    (h_vol : ∀ x ∈ S, 0 < θ x → vol x ≤ ENNReal.ofReal (16 * δ ^ 3 / Real.sin (θ x)))
    (h_vol_max : ∀ x ∈ S, vol x ≤ V / 2) :
    ∑ x ∈ S, vol x ≤
      ENNReal.ofReal (C_pack * 32 * Real.pi) * V * ENNReal.ofReal (Real.log (1 / δ)) := by
  let S_small := S.filter (fun x => θ x < δ)
  let S_large := S.filter (fun x => δ ≤ θ x)
  let S_big := S.filter (fun x => θ x ≥ Real.pi / 4)

  have h_part : S = S_small ∪ S_large := by
    ext x
    simp only [S_small, S_large, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h : θ x < δ
      · left; exact ⟨hx, h⟩
      · right; exact ⟨hx, by linarith⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

  have h_disj : Disjoint S_small S_large := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : θ x < δ := (Finset.mem_filter.mp hx1).2
    have h2 : δ ≤ θ x := (Finset.mem_filter.mp hx2).2
    linarith

  have h_log_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    have h : 1 / δ > 1 := by
      apply one_lt_one_div
      <;> linarith [hδ1]
    exact h

  have h_1000 : (1000 : ℝ) ≤ 1 / δ := by
    have h : δ ≤ 1 / 1000 := hδ1
    have h' : 0 < δ := hδ
    calc (1000 : ℝ)
      = 1 / (1 / 1000 : ℝ) := by norm_num
      _ ≤ 1 / δ := by gcongr

  have h_log_ge_one : (1 : ℝ) ≤ Real.log (1 / δ) := by
    have h1 : Real.log (1 / δ) ≥ Real.log 1000 := Real.log_le_log (by positivity) h_1000
    have h2 : Real.log 1000 > 1 := by
      have h3 : Real.exp 1 < (1000 : ℝ) := by
        have h4 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        linarith
      have h5 : Real.log (Real.exp 1) < Real.log 1000 := Real.log_lt_log (Real.exp_pos 1) h3
      have h6 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h6] at h5
      exact h5
    linarith

  -- Small angle bound
  have h_small_count : (S_small.card : ENNReal) ≤ ENNReal.ofReal C_pack := by
    have h1 : S_small ⊆ S.filter (fun x => θ x ≤ δ) := by
      intro x hx
      simp only [S_small, Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by linarith [hx.2]⟩
    have h2σ : 2 * (δ / 2) ≤ Real.pi / 2 := by
      have h1 : 2 * (δ / 2) = δ := by ring
      rw [h1]
      have h2 : δ ≤ 1 / 1000 := hδ1
      have h3 : (1 / 1000 : ℝ) < Real.pi / 2 := by
        have h4 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      linarith
    have h21 : (S.filter (fun x => θ x ≤ 2 * (δ / 2))).card ≤
        ENNReal.ofReal (C_pack * max 1 ((δ / 2) / δ)) :=
      h_count (δ / 2) (by positivity) h2σ
    have h22 : S.filter (fun x => θ x ≤ 2 * (δ / 2)) =
        S.filter (fun x => θ x ≤ δ) := by
      congr with x
      <;> ring
    rw [h22] at h21
    have h2 : (S.filter (fun x => θ x ≤ δ)).card ≤
        ENNReal.ofReal (C_pack * max 1 ((δ / 2) / δ)) := h21
    have h3 : max 1 ((δ / 2) / δ) = 1 := by
      have h4 : (δ / 2) / δ = 1 / 2 := by
        field_simp [hδ.ne'] <;> ring
      rw [h4] <;> norm_num
    rw [h3] at h2
    have h_simp : C_pack * 1 = C_pack := by ring
    rw [h_simp] at h2
    have h_cast : (S_small.card : ENNReal) ≤ ((S.filter (fun x => θ x ≤ δ)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h1
    exact h_cast.trans h2

  have h_small_sum : ∑ x ∈ S_small, vol x ≤
      ENNReal.ofReal C_pack * V * ENNReal.ofReal (Real.log (1 / δ)) := by
    have h_sum1 : ∑ x ∈ S_small, vol x ≤ (S_small.card : ENNReal) * (V / 2) := by
      calc
        ∑ x ∈ S_small, vol x
          ≤ ∑ x ∈ S_small, (V / 2) := Finset.sum_le_sum fun x hx =>
            h_vol_max x ((Finset.mem_filter.mp hx).1)
        _ = (S_small.card : ENNReal) * (V / 2) := by
          simp [Finset.sum_const] <;> ring
    have h4 : (V / 2 : ENNReal) ≤ V * ENNReal.ofReal (Real.log (1 / δ)) := by
      have h5 : (1 / 2 : ℝ) ≤ Real.log (1 / δ) := by
        have h6 : Real.log (1 / δ) ≥ Real.log 1000 := Real.log_le_log (by positivity) h_1000
        have h7 : Real.log 1000 > (1 / 2 : ℝ) := by
          have h8 : Real.log 1000 > Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
          have h9 : Real.log 4 > 1 := by
            have h10 : Real.exp 1 < (4 : ℝ) := by
              have h11 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
              linarith
            have h12 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) h10
            have h13 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
            rw [h13] at h12
            exact h12
          linarith
        linarith
      have h5' : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.log (1 / δ)) :=
        ENNReal.ofReal_le_ofReal h5
      calc
        (V / 2 : ENNReal) = V * ENNReal.ofReal (1 / 2 : ℝ) := by
          simp [div_eq_mul_inv] <;> ring
        _ ≤ V * ENNReal.ofReal (Real.log (1 / δ)) := by
          gcongr
    calc
      ∑ x ∈ S_small, vol x
        ≤ (S_small.card : ENNReal) * (V / 2) := h_sum1
      _ ≤ ENNReal.ofReal C_pack * (V / 2) := by gcongr
      _ ≤ ENNReal.ofReal C_pack * V * ENNReal.ofReal (Real.log (1 / δ)) := by
        rw [mul_assoc]
        gcongr

  -- Large angle bound (θ ≥ π/4)
  have h_big_vol : ∀ x ∈ S_big, vol x ≤ ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) := by
    intro x hx
    have hθ4 : Real.pi / 4 ≤ θ x := (Finset.mem_filter.mp hx).2
    have hθ5 : θ x ≤ Real.pi / 2 := hθ2 x ((Finset.mem_filter.mp hx).1)
    have hsin : Real.sin (θ x) ≥ Real.sqrt 2 / 2 := by
      have h6 : Real.sin (θ x) ≥ Real.sin (Real.pi / 4) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθ5 hθ4
      have h7 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [Real.sin_pi_div_four] <;> ring
      rw [h7] at h6; exact h6
    have h11 : 0 < Real.sin (θ x) := by
      have h12 : Real.sin (θ x) ≥ Real.sqrt 2 / 2 := hsin
      have h13 : 0 < Real.sqrt 2 / 2 := by positivity
      linarith
    have hpos : 0 < θ x := by linarith [Real.pi_pos]
    have h9 : vol x ≤ ENNReal.ofReal (16 * δ ^ 3 / Real.sin (θ x)) :=
      h_vol x ((Finset.mem_filter.mp hx).1) hpos
    have h10 : 16 * δ ^ 3 / Real.sin (θ x) ≤ 16 * Real.sqrt 2 * δ ^ 3 := by
      calc
        16 * δ ^ 3 / Real.sin (θ x)
          ≤ 16 * δ ^ 3 / (Real.sqrt 2 / 2) := by gcongr
        _ = 16 * Real.sqrt 2 * δ ^ 3 := by
          have hpos2 : 0 < Real.sqrt 2 := by positivity
          field_simp [hpos2.ne']
          <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact h9.trans (ENNReal.ofReal_le_ofReal h10)

  have h_big_count : (S_big.card : ENNReal) ≤ ENNReal.ofReal (C_pack * Real.pi / (4 * δ)) := by
    have h1 : S_big ⊆ S.filter (fun x => θ x ≤ Real.pi / 2) := by
      intro x hx
      simp only [S_big, Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hθ2 x hx.1⟩
    have h21 : (S.filter (fun x => θ x ≤ 2 * (Real.pi / 4))).card ≤
        ENNReal.ofReal (C_pack * max 1 ((Real.pi / 4) / δ)) :=
      h_count (Real.pi / 4) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h22 : S.filter (fun x => θ x ≤ 2 * (Real.pi / 4)) =
        S.filter (fun x => θ x ≤ Real.pi / 2) := by
      congr with x <;> ring
    rw [h22] at h21
    have h2 : (S.filter (fun x => θ x ≤ Real.pi / 2)).card ≤
        ENNReal.ofReal (C_pack * max 1 ((Real.pi / 4) / δ)) := h21
    have h3 : max 1 ((Real.pi / 4) / δ) = (Real.pi / 4) / δ := by
      have h4 : (1 : ℝ) ≤ (Real.pi / 4) / δ := by
        have h5 : δ ≤ 1 / 1000 := hδ1
        have h6 : 0 < δ := hδ
        have h7 : (Real.pi / 4) / δ ≥ (Real.pi / 4) / (1 / 1000) := by gcongr
        have h8 : (Real.pi / 4) / (1 / 1000) = 250 * Real.pi := by
          field_simp <;> ring
        rw [h8] at h7
        have h9 : (1 : ℝ) ≤ 250 * Real.pi := by
          have h10 : Real.pi > 3 := Real.pi_gt_three
          nlinarith
        linarith
      rw [max_eq_right h4]
    rw [h3] at h2
    have h4 : C_pack * ((Real.pi / 4) / δ) = C_pack * Real.pi / (4 * δ) := by ring
    rw [h4] at h2
    have h_cast : (S_big.card : ENNReal) ≤ ((S.filter (fun x => θ x ≤ Real.pi / 2)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h1
    exact h_cast.trans h2

  have h_big_sum : ∑ x ∈ S_big, vol x ≤
      ENNReal.ofReal C_pack * V *
        ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := by
    have h_sum1 : ∑ x ∈ S_big, vol x ≤
        (S_big.card : ENNReal) * ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) := by
      calc
        ∑ x ∈ S_big, vol x
          ≤ ∑ x ∈ S_big, ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) :=
            Finset.sum_le_sum fun x hx => h_big_vol x hx
        _ = (S_big.card : ENNReal) * ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) := by
          simp [Finset.sum_const] <;> ring
    have h_a : 0 ≤ C_pack * Real.pi / (4 * δ) := by positivity
    have h_b : 0 ≤ 16 * Real.sqrt 2 * δ ^ 3 := by positivity
    have h_prod : ENNReal.ofReal (C_pack * Real.pi / (4 * δ)) *
        ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) =
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2 * δ ^ 2) := by
      have h_eq1 : ENNReal.ofReal (C_pack * Real.pi / (4 * δ)) *
          ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) =
          ENNReal.ofReal ((C_pack * Real.pi / (4 * δ)) * (16 * Real.sqrt 2 * δ ^ 3)) := by
        rw [←ENNReal.ofReal_mul (hp := h_a)]
      rw [h_eq1]
      congr 1
      field_simp [hδ.ne'] <;> ring
    have h_factor : ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2 * δ ^ 2) =
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * ENNReal.ofReal (δ ^ 2) := by
      rw [←ENNReal.ofReal_mul (by positivity)] <;> ring
    have h_V_bound : ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2 * δ ^ 2) ≤
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V := by
      rw [h_factor]
      have h_nonneg : 0 ≤ ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) := by positivity
      exact mul_le_mul_of_nonneg_left hV_lower h_nonneg
    have h_one : (1 : ENNReal) ≤ ENNReal.ofReal (Real.log (1 / δ)) := by
      have h10 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h10]
      exact ENNReal.ofReal_le_ofReal h_log_ge_one
    have h_log_bound : ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V ≤
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V *
          ENNReal.ofReal (Real.log (1 / δ)) := by
      calc
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V
          = ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V * 1 := by ring
        _ ≤ ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V *
              ENNReal.ofReal (Real.log (1 / δ)) := by gcongr
    have h_final_eq : ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V *
        ENNReal.ofReal (Real.log (1 / δ)) =
        ENNReal.ofReal C_pack * V *
          ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := by
      have h_pos4 : 0 ≤ 4 * Real.pi * Real.sqrt 2 := by positivity
      have h1 : ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) =
          ENNReal.ofReal C_pack * ENNReal.ofReal (4 * Real.pi * Real.sqrt 2) := by
        have h_eq : C_pack * 4 * Real.pi * Real.sqrt 2 = C_pack * (4 * Real.pi * Real.sqrt 2) := by ring
        rw [h_eq]
        exact ENNReal.ofReal_mul (p := C_pack) (q := 4 * Real.pi * Real.sqrt 2) (hp := hC_nonneg)
      have h2 : ENNReal.ofReal (4 * Real.pi * Real.sqrt 2) *
          ENNReal.ofReal (Real.log (1 / δ)) =
          ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := by
        exact (ENNReal.ofReal_mul (p := 4 * Real.pi * Real.sqrt 2) (q := Real.log (1 / δ)) (hp := h_pos4)).symm
      calc
        ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V *
              ENNReal.ofReal (Real.log (1 / δ))
          = (ENNReal.ofReal C_pack * ENNReal.ofReal (4 * Real.pi * Real.sqrt 2)) * V *
                ENNReal.ofReal (Real.log (1 / δ)) := by rw [h1]
        _ = ENNReal.ofReal C_pack * V *
              (ENNReal.ofReal (4 * Real.pi * Real.sqrt 2) *
                ENNReal.ofReal (Real.log (1 / δ))) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
        _ = ENNReal.ofReal C_pack * V *
              ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := by
            rw [h2]
    calc
      ∑ x ∈ S_big, vol x
        ≤ (S_big.card : ENNReal) * ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) := h_sum1
      _ ≤ ENNReal.ofReal (C_pack * Real.pi / (4 * δ)) *
            ENNReal.ofReal (16 * Real.sqrt 2 * δ ^ 3) := by gcongr
      _ = ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2 * δ ^ 2) := h_prod
      _ ≤ ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V := h_V_bound
      _ ≤ ENNReal.ofReal (C_pack * 4 * Real.pi * Real.sqrt 2) * V *
            ENNReal.ofReal (Real.log (1 / δ)) := h_log_bound
      _ = ENNReal.ofReal C_pack * V *
            ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := h_final_eq

  -- Dyadic bands: N chosen so 2^N * δ ∈ (π/4, π/2]
  let N : ℕ := Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) + 1
  have hN_pos : 0 < N := by
    have h1 : 0 ≤ Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
      have h2 : Real.pi / (4 * δ) ≥ 1 := by
        have h3 : δ ≤ 1 / 1000 := hδ1
        calc Real.pi / (4 * δ)
          ≥ Real.pi / (4 * (1 / 1000)) := by gcongr
          _ = 250 * Real.pi := by ring
          _ ≥ 1 := by
            have h4 : Real.pi > 3 := Real.pi_gt_three
            nlinarith
      have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact div_nonneg (Real.log_nonneg h2) h5.le
    have h6 : 0 ≤ Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) := by
      exact Nat.zero_le _
    omega
  have hN_bound : (N : ℝ) ≤ 3 * Real.log (1 / δ) := by
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_nonneg_log : 0 ≤ Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
      have h21 : Real.pi / (4 * δ) ≥ 1 := by
        have h3 : δ ≤ 1 / 1000 := hδ1
        calc Real.pi / (4 * δ)
          ≥ Real.pi / (4 * (1 / 1000)) := by gcongr
          _ = 250 * Real.pi := by ring
          _ ≥ 1 := by have h4 : Real.pi > 3 := Real.pi_gt_three; nlinarith
      have h22 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact div_nonneg (Real.log_nonneg h21) h22.le
    have h1 : (N : ℝ) ≤ Real.log (Real.pi / (4 * δ)) / Real.log 2 + 1 := by
      have h2 : (Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) : ℝ) ≤
          Real.log (Real.pi / (4 * δ)) / Real.log 2 := Nat.floor_le h_nonneg_log
      simp [N] <;> linarith
    have h3 : Real.log (Real.pi / (4 * δ)) = Real.log (1 / δ) + Real.log (Real.pi / 4) := by
      have h4 : Real.pi / (4 * δ) = (1 / δ) * (Real.pi / 4) := by ring
      rw [h4, Real.log_mul (by positivity) (by positivity)] <;> ring
    have h4 : Real.log (Real.pi / 4) < 0 := by
      have h5 : 0 < Real.pi / 4 := by positivity
      have h6 : Real.pi / 4 < 1 := by
        have h7 : Real.pi < 4 := Real.pi_lt_four
        linarith
      exact Real.log_neg h5 h6
    have h5 : Real.log (Real.pi / (4 * δ)) / Real.log 2 < Real.log (1 / δ) / Real.log 2 := by
      rw [h3]
      have h6 : Real.log (1 / δ) + Real.log (Real.pi / 4) < Real.log (1 / δ) := by linarith
      gcongr
    have h7 : 1 / Real.log 2 ≤ 2 := by
      have h8 : Real.log 2 > 1 / 2 := by
        have h9 : Real.exp (1 / 2 : ℝ) < 2 := by
          have h10 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
            have h11 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
              rw [←Real.exp_add] <;> norm_num
            nlinarith
          have h12 : Real.exp 1 < (4 : ℝ) := by
            have h13 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
            linarith
          nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        have h14 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (Real.exp_pos _) h9
        have h15 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := Real.log_exp (1 / 2 : ℝ)
        rw [h15] at h14
        exact h14
      calc 1 / Real.log 2 ≤ 1 / (1 / 2) := by gcongr
           _ = 2 := by norm_num
    have h8 : Real.log (1 / δ) ≥ 1 := h_log_ge_one
    have h9 : (N : ℝ) < Real.log (1 / δ) / Real.log 2 + 1 := by linarith
    have h10 : Real.log (1 / δ) / Real.log 2 + 1 ≤ 3 * Real.log (1 / δ) := by
      have h11 : Real.log (1 / δ) / Real.log 2 ≤ 2 * Real.log (1 / δ) := by
        calc Real.log (1 / δ) / Real.log 2
          = Real.log (1 / δ) * (1 / Real.log 2) := by field_simp <;> ring
        _ ≤ Real.log (1 / δ) * 2 := by gcongr
        _ = 2 * Real.log (1 / δ) := by ring
      have h12 : (1 : ℝ) ≤ Real.log (1 / δ) := h8
      linarith
    exact h9.le.trans h10

  let band (k : ℕ) : Finset α :=
    S.filter (fun x => (2 : ℝ)^k * δ ≤ θ x ∧ θ x < (2 : ℝ)^(k+1) * δ)

  have h_bands_disjoint : ∀ (k l : ℕ), k ∈ Finset.range N → l ∈ Finset.range N → k ≠ l → Disjoint (band k) (band l) := by
    intro k l _ _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    have h11 : (2 : ℝ)^k * δ ≤ θ x := h1.1
    have h12 : θ x < (2 : ℝ)^(k + 1) * δ := h1.2
    have h21 : (2 : ℝ)^l * δ ≤ θ x := h2.1
    have h22 : θ x < (2 : ℝ)^(l + 1) * δ := h2.2
    by_cases h : k < l
    · have h3 : (2 : ℝ)^(k + 1) * δ ≤ (2 : ℝ)^l * δ := by
        have h4 : k + 1 ≤ l := by omega
        have h5 : (2 : ℝ)^(k + 1) ≤ (2 : ℝ)^l := by
          gcongr <;> norm_num
        gcongr
      linarith
    · have h' : l < k := by omega
      have h3 : (2 : ℝ)^(l + 1) * δ ≤ (2 : ℝ)^k * δ := by
        have h4 : l + 1 ≤ k := by omega
        have h5 : (2 : ℝ)^(l + 1) ≤ (2 : ℝ)^k := by gcongr <;> norm_num
        gcongr
      linarith

  have h_band_bound : ∀ k ∈ Finset.range N, ∑ x ∈ band k, vol x ≤
      ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) := by
    intro k hk
    have h_valid : (2 : ℝ)^(k + 1) * δ ≤ Real.pi / 2 := by
      have hk_lt : k < N := Finset.mem_range.mp hk
      have h1 : k ≤ Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) := by
        simp [N] at hk_lt <;> omega
      have h_nonneg : 0 ≤ Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
        have h21 : Real.pi / (4 * δ) ≥ 1 := by
          have h3 : δ ≤ 1 / 1000 := hδ1
          calc Real.pi / (4 * δ)
            ≥ Real.pi / (4 * (1 / 1000)) := by gcongr
            _ = 250 * Real.pi := by ring
            _ ≥ 1 := by have h4 : Real.pi > 3 := Real.pi_gt_three; nlinarith
        have h22 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        exact div_nonneg (Real.log_nonneg h21) h22.le
      have h_floor_le : (Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) : ℝ) ≤
          Real.log (Real.pi / (4 * δ)) / Real.log 2 := Nat.floor_le h_nonneg
      have h2 : (k : ℝ) ≤ Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
        have h1' : (k : ℝ) ≤ (Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) : ℝ) := by exact_mod_cast h1
        exact le_trans h1' h_floor_le
      have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h5 : (k : ℝ) * Real.log 2 ≤ Real.log (Real.pi / (4 * δ)) := by
        calc (k : ℝ) * Real.log 2
          ≤ (Real.log (Real.pi / (4 * δ)) / Real.log 2) * Real.log 2 := by gcongr
        _ = Real.log (Real.pi / (4 * δ)) := by
          field_simp [h4.ne'] <;> ring
      have h6 : (2 : ℝ)^k ≤ Real.pi / (4 * δ) := by
        have h7 : Real.log ((2 : ℝ)^k) = (k : ℝ) * Real.log 2 := by
          rw [Real.log_pow] <;> ring
        have h8 : Real.log ((2 : ℝ)^k) ≤ Real.log (Real.pi / (4 * δ)) := by
          rw [h7] <;> exact h5
        have h9 : 0 < (2 : ℝ)^k := by positivity
        have h10 : 0 < Real.pi / (4 * δ) := by positivity
        exact (Real.log_le_log_iff h9 h10).mp h8
      calc (2 : ℝ)^(k + 1) * δ
        = 2 * (2 : ℝ)^k * δ := by ring
      _ ≤ 2 * (Real.pi / (4 * δ)) * δ := by gcongr
      _ = Real.pi / 2 := by
        field_simp [hδ.ne'] <;> ring
    have h_count_k : (band k).card ≤ ENNReal.ofReal (C_pack * (2 : ℝ)^k) := by
      have h1 : band k ⊆ S.filter (fun x => θ x ≤ 2 * ((2 : ℝ)^k * δ)) := by
        intro x hx
        have h2 := (Finset.mem_filter.mp hx).2
        simp only [band, Finset.mem_filter] at hx ⊢
        have h3 : θ x ≤ 2 * ((2 : ℝ)^k * δ) := by
          have h4 : 2 * ((2 : ℝ)^k * δ) = (2 : ℝ)^(k + 1) * δ := by ring
          rw [h4]
          exact le_of_lt h2.2
        exact ⟨hx.1, h3⟩
      have hσ2 : 2 * ((2 : ℝ)^k * δ) ≤ Real.pi / 2 := by
        have h_eq : 2 * ((2 : ℝ)^k * δ) = (2 : ℝ)^(k + 1) * δ := by ring
        rw [h_eq]
        exact h_valid
      have h2 := h_count ((2 : ℝ)^k * δ) (by positivity) hσ2
      have h3 : max 1 (((2 : ℝ)^k * δ) / δ) = (2 : ℝ)^k := by
        have h4 : ((2 : ℝ)^k * δ) / δ = (2 : ℝ)^k := by
          field_simp [hδ.ne'] <;> ring
        rw [h4]
        have h5 : (1 : ℝ) ≤ (2 : ℝ)^k := by
          have h6 : (0 : ℝ) ≤ (k : ℝ) := by positivity
          have h7 : (1 : ℝ) ≤ (2 : ℝ)^(k : ℝ) := by
            apply one_le_rpow <;> norm_num <;> linarith
          exact_mod_cast h7
        rw [max_eq_right h5]
      rw [h3] at h2
      have h_cast : ((band k).card : ENNReal) ≤ ((S.filter (fun x => θ x ≤ 2 * ((2 : ℝ)^k * δ))).card : ENNReal) := by
        exact_mod_cast Finset.card_le_card h1
      exact h_cast.trans h2
    have h_vol_k : ∀ x ∈ band k, vol x ≤
        ENNReal.ofReal (8 * Real.pi * δ ^ 2 / (2 : ℝ)^k) := by
      intro x hx
      have hθ_ge : (2 : ℝ)^k * δ ≤ θ x := (Finset.mem_filter.mp hx).2.1
      have hθ_pos : 0 < θ x := by
        have hpos1 : 0 < (2 : ℝ)^k * δ := by positivity
        linarith [hθ_ge]
      have h1 : vol x ≤ ENNReal.ofReal (16 * δ ^ 3 / Real.sin (θ x)) :=
        h_vol x ((Finset.mem_filter.mp hx).1) hθ_pos
      have h2 : Real.sin (θ x) ≥ 2 * (θ x) / Real.pi :=
        sin_lower_bound (hθ1 x ((Finset.mem_filter.mp hx).1)) (hθ2 x ((Finset.mem_filter.mp hx).1))
      have h3 : 2 * (θ x) / Real.pi ≥ 2 * ((2 : ℝ)^k * δ) / Real.pi := by gcongr
      have h4 : 16 * δ ^ 3 / Real.sin (θ x) ≤ 8 * Real.pi * δ ^ 2 / (2 : ℝ)^k := by
        have hθ_lt_pi : θ x < Real.pi := by
          have h : θ x ≤ Real.pi / 2 := hθ2 x ((Finset.mem_filter.mp hx).1)
          have hpi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
          linarith
        have h5 : 0 < Real.sin (θ x) := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
        have h6 : Real.sin (θ x) ≥ 2 * (2 : ℝ)^k * δ / Real.pi := by
          have h3' : (2 : ℝ)^k * δ ≤ θ x := hθ_ge
          have h4' : 2 * ((2 : ℝ)^k * δ) ≤ 2 * (θ x) := by
            exact mul_le_mul_of_nonneg_left h3' (by norm_num)
          have h5' : 2 * ((2 : ℝ)^k * δ) / Real.pi ≤ 2 * (θ x) / Real.pi := by
            exact div_le_div_of_nonneg_right h4' (by positivity)
          have h2' : 2 * (θ x) / Real.pi ≤ Real.sin (θ x) := h2
          have h_goal : 2 * ((2 : ℝ)^k * δ) / Real.pi ≤ Real.sin (θ x) := le_trans h5' h2'
          have h_final : Real.sin (θ x) ≥ 2 * (2 : ℝ)^k * δ / Real.pi := by
            have h_eq : 2 * ((2 : ℝ)^k * δ) / Real.pi = 2 * (2 : ℝ)^k * δ / Real.pi := by ring
            rw [h_eq] at h_goal
            exact h_goal
          exact h_final
        calc
          16 * δ ^ 3 / Real.sin (θ x)
            ≤ 16 * δ ^ 3 / (2 * (2 : ℝ)^k * δ / Real.pi) := by gcongr
          _ = 8 * Real.pi * δ ^ 2 / (2 : ℝ)^k := by
            field_simp [hδ.ne', show (0 : ℝ) < (2 : ℝ)^k by positivity] <;> ring
      exact h1.trans (ENNReal.ofReal_le_ofReal h4)
    calc
      ∑ x ∈ band k, vol x
        ≤ ∑ x ∈ band k, ENNReal.ofReal (8 * Real.pi * δ ^ 2 / (2 : ℝ)^k) :=
          Finset.sum_le_sum h_vol_k
      _ = (band k).card * ENNReal.ofReal (8 * Real.pi * δ ^ 2 / (2 : ℝ)^k) := by
        simp [Finset.sum_const] <;> ring
      _ ≤ ENNReal.ofReal (C_pack * (2 : ℝ)^k) *
            ENNReal.ofReal (8 * Real.pi * δ ^ 2 / (2 : ℝ)^k) := by gcongr
      _ = ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) := by
        have hpos : 0 ≤ C_pack * (2 : ℝ)^k := by positivity
        have hpos2 : (0 : ℝ) < (2 : ℝ)^k := by positivity
        rw [←ENNReal.ofReal_mul (p := C_pack * (2 : ℝ)^k) (q := 8 * Real.pi * δ ^ 2 / (2 : ℝ)^k) (hp := hpos)]
        <;> congr 1 <;> field_simp [hpos2.ne'] <;> ring

  let S_mid := S_large.filter (fun x => x ∉ S_big)
  have h_cover : S_mid ⊆ Finset.biUnion (Finset.range N) band := by
    intro x hx
    have hx_large : x ∈ S_large := (Finset.mem_filter.mp hx).1
    have hxS : x ∈ S := (Finset.mem_filter.mp hx_large).1
    have hθ_ge : δ ≤ θ x := (Finset.mem_filter.mp hx_large).2
    have h_not_big : x ∉ S_big := (Finset.mem_filter.mp hx).2
    have hθ_lt : θ x < Real.pi / 4 := by
      simp only [S_big, Finset.mem_filter] at h_not_big
      have h : ¬(x ∈ S ∧ Real.pi / 4 ≤ θ x) := h_not_big
      have h' : ¬(Real.pi / 4 ≤ θ x) := by
        intro hge
        exact h ⟨hxS, hge⟩
      exact lt_of_not_ge h'
    let k : ℕ := Nat.floor (Real.log ((θ x) / δ) / Real.log 2)
    have h_pos_xδ : 0 < (θ x) / δ := by
      have hpos1 : 0 < δ := hδ
      have hpos2 : 0 < θ x := by linarith [hθ_ge]
      exact div_pos hpos2 hpos1
    have h_ge_one : (θ x) / δ ≥ 1 := by
      have h2 : δ ≤ θ x := hθ_ge
      have h3 : 0 < δ := hδ
      calc (θ x) / δ ≥ δ / δ := by gcongr
        _ = 1 := by field_simp [h3.ne'] <;> ring
    have h_nonneg_log : 0 ≤ Real.log ((θ x) / δ) / Real.log 2 := by
      have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact div_nonneg (Real.log_nonneg h_ge_one) h4.le
    have hk1 : (2 : ℝ)^k ≤ (θ x) / δ := by
      have h : (k : ℝ) ≤ Real.log ((θ x) / δ) / Real.log 2 := Nat.floor_le h_nonneg_log
      have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h5 : (2 : ℝ)^(k : ℝ) ≤ (2 : ℝ)^(Real.log ((θ x) / δ) / Real.log 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h
      have h6 : (2 : ℝ)^(Real.log ((θ x) / δ) / Real.log 2) = (θ x) / δ := by
        have h7 : Real.log ((θ x) / δ) / Real.log 2 = Real.logb 2 ((θ x) / δ) := by
          rw [Real.logb] <;> ring
        rw [h7]
        apply Real.rpow_logb <;> norm_num <;> exact h_pos_xδ
      rw [h6] at h5
      have h_eq1 : (2 : ℝ)^(k : ℝ) = (2 : ℝ)^k := by norm_cast
      rw [h_eq1] at h5
      exact h5
    have hk2 : (θ x) / δ < (2 : ℝ)^(k + 1) := by
      have h : Real.log ((θ x) / δ) / Real.log 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
      have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h5 : (2 : ℝ)^(Real.log ((θ x) / δ) / Real.log 2) < (2 : ℝ)^((k : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
      have h6 : (2 : ℝ)^(Real.log ((θ x) / δ) / Real.log 2) = (θ x) / δ := by
        have h7 : Real.log ((θ x) / δ) / Real.log 2 = Real.logb 2 ((θ x) / δ) := by
          rw [Real.logb] <;> ring
        rw [h7]
        apply Real.rpow_logb <;> norm_num <;> exact h_pos_xδ
      rw [h6] at h5
      have h_eq2 : (2 : ℝ)^((k : ℝ) + 1) = (2 : ℝ)^(k + 1) := by norm_cast
      rw [h_eq2] at h5
      exact h5
    have hk_in : k ∈ Finset.range N := by
      have h1 : (k : ℝ) ≤ Real.log ((θ x) / δ) / Real.log 2 := Nat.floor_le h_nonneg_log
      have h2 : (θ x) / δ < Real.pi / (4 * δ) := by
        have h21 : (θ x) / δ < (Real.pi / 4) / δ := by gcongr <;> linarith [hθ_lt]
        have h22 : (Real.pi / 4) / δ = Real.pi / (4 * δ) := by ring
        linarith
      have h3 : Real.log ((θ x) / δ) < Real.log (Real.pi / (4 * δ)) := Real.log_lt_log (by positivity) h2
      have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h5 : (k : ℝ) < Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
        calc (k : ℝ)
          ≤ Real.log ((θ x) / δ) / Real.log 2 := h1
        _ < Real.log (Real.pi / (4 * δ)) / Real.log 2 := by gcongr
      have h6 : (N : ℝ) > Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
        have h7 : (N : ℝ) = (Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) : ℝ) + 1 := by
          simp [N] <;> norm_cast
        rw [h7]
        have h8 : ((Nat.floor (Real.log (Real.pi / (4 * δ)) / Real.log 2) : ℝ) + 1) >
            Real.log (Real.pi / (4 * δ)) / Real.log 2 := by
          have h9 := Nat.lt_floor_add_one (Real.log (Real.pi / (4 * δ)) / Real.log 2)
          exact h9
        exact h8
      have h9 : (k : ℝ) < (N : ℝ) := by linarith
      have h10 : k < N := Nat.cast_lt.mp h9
      simpa [Finset.mem_range] using h10
    have h_x_in_band : x ∈ band k := by
      simp only [band, Finset.mem_filter]
      have h5 : (2 : ℝ)^k * δ ≤ θ x := by
        have h6 : (2 : ℝ)^k ≤ (θ x) / δ := hk1
        have h7 : 0 < δ := hδ
        calc (2 : ℝ)^k * δ
          ≤ ((θ x) / δ) * δ := by gcongr
        _ = θ x := by field_simp [h7.ne'] <;> ring
      have h8 : θ x < (2 : ℝ)^(k + 1) * δ := by
        have h9 : (θ x) / δ < (2 : ℝ)^(k + 1) := hk2
        have h10 : 0 < δ := hδ
        calc θ x
          = ((θ x) / δ) * δ := by field_simp [h10.ne'] <;> ring
        _ < (2 : ℝ)^(k + 1) * δ := by gcongr
      exact ⟨hxS, h5, h8⟩
    exact Finset.mem_biUnion.mpr ⟨k, hk_in, h_x_in_band⟩

  have h_mid_sum : ∑ x ∈ S_mid, vol x ≤
      (N : ENNReal) * ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) := by
    calc
      ∑ x ∈ S_mid, vol x
        ≤ ∑ x ∈ Finset.biUnion (Finset.range N) band, vol x :=
          Finset.sum_le_sum_of_subset_of_nonneg h_cover (fun _ _ _ => by positivity)
      _ = ∑ k ∈ Finset.range N, ∑ x ∈ band k, vol x := by
        have h_disj' : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, i ≠ j → Disjoint (band i) (band j) := by
          intro i hi j hj hij
          exact h_bands_disjoint i j hi hj hij
        rw [Finset.sum_biUnion h_disj']
      _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) :=
          Finset.sum_le_sum fun k hk => h_band_bound k hk
      _ = (N : ENNReal) * ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range]
        <;> simp [mul_comm]

  have h_mid_final : ∑ x ∈ S_mid, vol x ≤
      ENNReal.ofReal C_pack * V * ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) := by
    have h1 : (N : ENNReal) ≤ ENNReal.ofReal (3 * Real.log (1 / δ)) := by
      have h1' : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by norm_cast
      rw [h1']
      exact ENNReal.ofReal_le_ofReal hN_bound
    have h2 : ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) ≤
        ENNReal.ofReal C_pack * V * ENNReal.ofReal (8 * Real.pi) := by
      have h_pos1 : 0 ≤ C_pack := hC_nonneg
      have h_pos2 : 0 ≤ 8 * Real.pi := by positivity
      have h_eq1 : ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) =
          ENNReal.ofReal C_pack * ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (δ ^ 2) := by
        have h_a : ENNReal.ofReal (C_pack * (8 * Real.pi * δ ^ 2)) =
            ENNReal.ofReal C_pack * ENNReal.ofReal (8 * Real.pi * δ ^ 2) :=
          ENNReal.ofReal_mul h_pos1
        have h_b : ENNReal.ofReal (8 * Real.pi * δ ^ 2) =
            ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (δ ^ 2) :=
          ENNReal.ofReal_mul h_pos2
        have h_c : C_pack * 8 * Real.pi * δ ^ 2 = C_pack * (8 * Real.pi * δ ^ 2) := by ring
        rw [h_c, h_a, h_b]
        <;> exact (mul_assoc (ENNReal.ofReal C_pack)
          (ENNReal.ofReal (8 * Real.pi)) (ENNReal.ofReal (δ ^ 2))).symm
      rw [h_eq1]
      have h4 : ENNReal.ofReal (δ ^ 2) ≤ V := hV_lower
      have h5 : ENNReal.ofReal C_pack * ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (δ ^ 2) ≤
          ENNReal.ofReal C_pack * ENNReal.ofReal (8 * Real.pi) * V := by gcongr
      have h6 : ENNReal.ofReal C_pack * ENNReal.ofReal (8 * Real.pi) * V =
          ENNReal.ofReal C_pack * V * ENNReal.ofReal (8 * Real.pi) := by
        set a : ENNReal := ENNReal.ofReal C_pack with ha
        set b : ENNReal := ENNReal.ofReal (8 * Real.pi) with hb
        have h : a * b * V = a * V * b := by
          calc a * b * V
            = a * (b * V) := by exact mul_assoc a b V
          _ = a * (V * b) := by rw [mul_comm b V]
          _ = a * V * b := by exact (mul_assoc a V b).symm
        exact h
      rw [h6] at h5
      exact h5
    calc
      ∑ x ∈ S_mid, vol x
        ≤ (N : ENNReal) * ENNReal.ofReal (C_pack * 8 * Real.pi * δ ^ 2) := h_mid_sum
      _ ≤ ENNReal.ofReal (3 * Real.log (1 / δ)) *
            (ENNReal.ofReal C_pack * V * ENNReal.ofReal (8 * Real.pi)) := by gcongr
      _ = ENNReal.ofReal C_pack * V *
            ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) := by
          have h_pos3 : 0 ≤ 3 * Real.log (1 / δ) := by positivity
          have h_eq2 : ENNReal.ofReal (3 * Real.log (1 / δ)) * ENNReal.ofReal (8 * Real.pi) =
              ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) := by
            have h_real : 3 * Real.log (1 / δ) * (8 * Real.pi) = 24 * Real.pi * Real.log (1 / δ) := by ring
            have h_mul : ENNReal.ofReal (3 * Real.log (1 / δ)) * ENNReal.ofReal (8 * Real.pi) =
                ENNReal.ofReal ((3 * Real.log (1 / δ)) * (8 * Real.pi)) := by
              let p : ℝ := 3 * Real.log (1 / δ)
              let q : ℝ := 8 * Real.pi
              have hpos : 0 ≤ p := h_pos3
              have h : ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := ENNReal.ofReal_mul hpos
              exact h.symm
            rw [h_mul]
            <;> congr
            <;> exact h_real
          have h_comm : ENNReal.ofReal (3 * Real.log (1 / δ)) * (ENNReal.ofReal C_pack * V * ENNReal.ofReal (8 * Real.pi)) =
              ENNReal.ofReal C_pack * V * (ENNReal.ofReal (3 * Real.log (1 / δ)) * ENNReal.ofReal (8 * Real.pi)) := by
            set x : ENNReal := ENNReal.ofReal (3 * Real.log (1 / δ)) with hx
            set a : ENNReal := ENNReal.ofReal C_pack with ha
            set b : ENNReal := ENNReal.ofReal (8 * Real.pi) with hb
            have h1 : x * (a * V * b) = (a * V * b) * x := mul_comm x (a * V * b)
            rw [h1]
            have h2 : (a * V * b) * x = a * V * (x * b) := by
              have h3 : (a * V * b) * x = (a * V) * (b * x) := by
                exact mul_assoc (a * V) b x
              rw [h3]
              have h4 : b * x = x * b := mul_comm b x
              rw [h4]
              <;> rfl
            exact h2
          rw [h_comm, h_eq2]

  have h_large_sum : ∑ x ∈ S_large, vol x ≤
      ENNReal.ofReal C_pack * V *
        ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
    have h_disj2 : Disjoint S_mid S_big := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h3 : x ∉ S_big := (Finset.mem_filter.mp hx1).2
      contradiction
    have h_union : S_large ⊆ S_mid ∪ S_big := by
      intro x hx
      by_cases h : x ∈ S_big
      · simpa [Finset.mem_union] using Or.inr h
      · have h' : x ∈ S_mid := by
          simp only [S_mid, Finset.mem_filter]
          exact ⟨hx, h⟩
        simpa [Finset.mem_union] using Or.inl h'
    have hpos_log : 0 ≤ Real.log (1 / δ) := by positivity
    have h_eq : ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) +
        ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) =
        ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
      have h1 : 0 ≤ 24 * Real.pi * Real.log (1 / δ) := by positivity
      have h2 : 0 ≤ 4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ) := by positivity
      rw [←ENNReal.ofReal_add h1 h2]
      <;> ring
    calc
      ∑ x ∈ S_large, vol x
        ≤ ∑ x ∈ S_mid ∪ S_big, vol x :=
          Finset.sum_le_sum_of_subset_of_nonneg h_union (fun _ _ _ => by positivity)
      _ = ∑ x ∈ S_mid, vol x + ∑ x ∈ S_big, vol x := by
          rw [Finset.sum_union h_disj2]
      _ ≤ ENNReal.ofReal C_pack * V * ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) +
            ENNReal.ofReal C_pack * V *
              ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ)) := by gcongr
      _ = ENNReal.ofReal C_pack * V *
            (ENNReal.ofReal (24 * Real.pi * Real.log (1 / δ)) +
              ENNReal.ofReal (4 * Real.pi * Real.sqrt 2 * Real.log (1 / δ))) := by
          simp [mul_add, mul_assoc, mul_comm, mul_left_comm] <;> ring
      _ = ENNReal.ofReal C_pack * V *
            ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
          rw [h_eq]

  have h_total : ∑ x ∈ S, vol x ≤
      ENNReal.ofReal C_pack * V *
        ENNReal.ofReal ((1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
    rw [h_part]
    rw [Finset.sum_union h_disj]
    have h1 : ∑ x ∈ S_small, vol x ≤
        ENNReal.ofReal C_pack * V * ENNReal.ofReal (Real.log (1 / δ)) := h_small_sum
    have h2 : ∑ x ∈ S_large, vol x ≤
        ENNReal.ofReal C_pack * V *
          ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := h_large_sum
    have hpos_log : 0 ≤ Real.log (1 / δ) := by positivity
    have h_eq1 : ENNReal.ofReal (Real.log (1 / δ)) =
        ENNReal.ofReal (1 * Real.log (1 / δ)) := by
      have h : (1 : ℝ) * Real.log (1 / δ) = Real.log (1 / δ) := by ring
      rw [h]
    have h_eq2 : ENNReal.ofReal (Real.log (1 / δ)) +
        ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) =
        ENNReal.ofReal ((1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
      have h1 : 0 ≤ Real.log (1 / δ) := by positivity
      have h2 : 0 ≤ (24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ) := by positivity
      have h_real : Real.log (1 / δ) + (24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ) =
          (1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ) := by ring
      rw [←ENNReal.ofReal_add h1 h2]
      <;> congr
      <;> exact h_real
    calc
      ∑ x ∈ S_small, vol x + ∑ x ∈ S_large, vol x
        ≤ ENNReal.ofReal C_pack * V * ENNReal.ofReal (Real.log (1 / δ)) +
            ENNReal.ofReal C_pack * V *
              ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by gcongr
      _ = ENNReal.ofReal C_pack * V *
            (ENNReal.ofReal (Real.log (1 / δ)) +
              ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ))) := by
          have h_factor : ENNReal.ofReal C_pack * V * ENNReal.ofReal (Real.log (1 / δ)) +
              ENNReal.ofReal C_pack * V * ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) =
              ENNReal.ofReal C_pack * V * (ENNReal.ofReal (Real.log (1 / δ)) +
                ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ))) := by
            have h : (ENNReal.ofReal C_pack * V) * (ENNReal.ofReal (Real.log (1 / δ)) +
                ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ))) =
                (ENNReal.ofReal C_pack * V) * ENNReal.ofReal (Real.log (1 / δ)) +
                (ENNReal.ofReal C_pack * V) * ENNReal.ofReal ((24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
              rw [mul_add]
            exact h.symm
          exact h_factor
      _ = ENNReal.ofReal C_pack * V *
            ENNReal.ofReal ((1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) := by
          rw [h_eq2]

  have h_final : ENNReal.ofReal C_pack * V *
        ENNReal.ofReal ((1 + 24 * Real.pi + 4 * Real.pi * Real.sqrt 2) * Real.log (1 / δ)) ≤
      ENNReal.ofReal (C_pack * 32 * Real.pi) * V *
        ENNReal.ofReal (Real.log (1 / δ)) :=
    enoreal_final_bound C_pack hC_nonneg V δ hδ hδ1
  exact h_total.trans h_final

-- ============================================================================
-- Main intersection sum bound
-- ============================================================================

theorem intersection_sum_bound
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {n : Point3} {C0 C_KT : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (h_plane : LiesInTwoPlaneNeighborhood F n C0)
    (hKT : Kakeya.KatzTaoConvexWolffBound F C_KT)
    (h_ess_dist : F.IsEssentiallyDistinct)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ F)
    (V : ENNReal)
    (hC0 : 0 ≤ C0) (hCKT : 0 ≤ C_KT)
    (hV_all : ∀ U ∈ F, U.volume ≤ V)
    (hV_lower : ENNReal.ofReal (δ ^ 2) ≤ V) :
    ∑ U ∈ F.erase T,
      MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) ≤
    (ENNReal.ofReal ((2000 * (C0 + 1) * C_KT) * 32 * Real.pi)) * V *
      ENNReal.ofReal (Real.log (1 / δ)) := by
  classical
  let C_pack : ℝ := 2000 * (C0 + 1) * C_KT
  have hC_pack : 0 ≤ C_pack := by positivity
  let S_inter := (F.erase T).filter (fun U => (T.carrier ∩ U.carrier).Nonempty)
  have h_sum_eq : ∑ U ∈ F.erase T,
      MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) =
      ∑ U ∈ S_inter, MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) := by
    have h_zero : ∀ U ∈ F.erase T, U ∉ S_inter →
        MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) = 0 := by
      intro U hU h_not
      have h9 : ¬(T.carrier ∩ U.carrier).Nonempty := by
        by_contra h
        have h10 : U ∈ S_inter := by
          simp only [S_inter, Finset.mem_filter] <;> exact ⟨hU, h⟩
        exact h_not h10
      have h10 : T.carrier ∩ U.carrier = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h9
      have h11 : Y.carrier T ∩ Y.carrier U ⊆ T.carrier ∩ U.carrier :=
        Set.inter_subset_inter (Y.subset_tube hT)
          (Y.subset_tube (Finset.mem_of_mem_erase hU))
      have h12 : Y.carrier T ∩ Y.carrier U = ∅ := by
        rw [h10] at h11
        simpa using h11
      rw [h12] <;> simp
    have hS : S_inter ⊆ F.erase T := by
      simp [S_inter] <;> tauto
    exact Eq.symm (Finset.sum_subset hS h_zero)
  have hS_inter : S_inter ⊆ F.erase T := by
    simp [S_inter] <;> tauto
  have h_interS : ∀ U ∈ S_inter, (T.carrier ∩ U.carrier).Nonempty :=
    fun U hU => (Finset.mem_filter.mp hU).2
  have h_sub : ∀ U ∈ S_inter,
      MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) ≤
      MeasureTheory.volume (T.carrier ∩ U.carrier) := by
    intro U hU
    have hU' : U ∈ F.erase T := hS_inter hU
    apply MeasureTheory.measure_mono
    exact Set.inter_subset_inter (Y.subset_tube hT)
      (Y.subset_tube (Finset.mem_of_mem_erase hU'))
  have h_vol_max : ∀ U ∈ S_inter,
      MeasureTheory.volume (T.carrier ∩ U.carrier) ≤ V / 2 := by
    intro U hU
    have hU' : U ∈ F.erase T := hS_inter hU
    have hU_in_F : U ∈ F := Finset.mem_of_mem_erase hU'
    have h_ne : T ≠ U := by
      intro h
      have h_contra : U ∈ F.erase T := hU'
      rw [h] at h_contra <;> simp at h_contra
    have h_ess := h_ess_dist hT hU_in_F h_ne
    have h9 : max T.volume U.volume ≤ V := max_le (hV_all T hT) (hV_all U hU_in_F)
    have h10 : (2 : ENNReal)⁻¹ * max T.volume U.volume ≤ (2 : ENNReal)⁻¹ * V :=
      mul_le_mul_of_nonneg_left h9 (by positivity)
    have h11 : (2 : ENNReal)⁻¹ * V = V / 2 := by simp [div_eq_mul_inv, mul_comm]
    have h12 : (2 : ENNReal)⁻¹ * max T.volume U.volume ≤ V / 2 := by
      calc
        (2 : ENNReal)⁻¹ * max T.volume U.volume
          ≤ (2 : ENNReal)⁻¹ * V := h10
        _ = V / 2 := h11
    exact h_ess.trans h12
  have h_count' : ∀ σ : ℝ, 0 ≤ σ → 2 * σ ≤ Real.pi / 2 →
      (S_inter.filter (fun U => effectiveAngle T U ≤ 2 * σ)).card ≤
        ENNReal.ofReal (C_pack * max 1 (σ / δ)) :=
    fun σ hσ1 hσ2 =>
      direction_band_count hδ (by linarith) h_plane hKT hC0 hCKT T hT
        S_inter hS_inter h_interS hσ1 hσ2
  have h_vol' : ∀ U ∈ S_inter, 0 < effectiveAngle T U →
      MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
        ENNReal.ofReal (16 * δ ^ 3 / Real.sin (effectiveAngle T U)) := by
    intro U hU hpos
    have hle : effectiveAngle T U ≤ Real.pi / 2 := effectiveAngle_le_pi2 T U
    exact intersection_volume_at_angle hδ hδ1 T U (effectiveAngle T U) hpos hle rfl
  have h_main := dyadic_sum_bound
    (S := S_inter)
    (θ := effectiveAngle T) (vol := fun U => MeasureTheory.volume (T.carrier ∩ U.carrier))
    hδ hδ1
    (fun U _ => effectiveAngle_nonneg T U)
    (fun U _ => effectiveAngle_le_pi2 T U)
    C_pack hC_pack
    h_count'
    V hV_lower h_vol' h_vol_max
  calc
    ∑ U ∈ F.erase T, MeasureTheory.volume (Y.carrier T ∩ Y.carrier U)
      = ∑ U ∈ S_inter, MeasureTheory.volume (Y.carrier T ∩ Y.carrier U) := h_sum_eq
    _ ≤ ∑ U ∈ S_inter, MeasureTheory.volume (T.carrier ∩ U.carrier) :=
        Finset.sum_le_sum h_sub
    _ ≤ _ := h_main

end Kakeya.Hairbrush
