module

/-
  Good scale transfer: IsRegularBetweenScales under homothety rescaling.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Uniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Plane
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Ratio of two dyadic scales is a natural number when first ≥ second. -/
lemma dyadicScales_ratio_nat {x y : ℝ} (hx : x ∈ dyadicScales) (hy : y ∈ dyadicScales)
    (hxy : y ≤ x) : ∃ (a : ℕ), x / y = (a : ℝ) := by
  rcases hx with ⟨m, hm⟩
  rcases hy with ⟨n, hn⟩
  have hmn : m ≤ n := by
    have h : (2 : ℝ)^(-(m : ℤ)) ≥ (2 : ℝ)^(-(n : ℤ)) := by
      simpa [hm, hn] using hxy
    by_contra h2
    have h3 : (n : ℤ) < (m : ℤ) := by omega
    have h4 : (2 : ℝ)^(-(n : ℤ)) > (2 : ℝ)^(-(m : ℤ)) := by
      gcongr <;> norm_num
    linarith
  let k : ℕ := n - m
  refine ⟨2 ^ k, ?_⟩
  have h_main : x / y = (2 : ℝ)^(k : ℤ) := by
    rw [hm, hn]
    have h_inv : ((2 : ℝ)^(-(n : ℤ)))⁻¹ = (2 : ℝ)^((n : ℤ)) := by
      rw [← zpow_neg] <;> ring_nf
    have h_div : (2 : ℝ)^(-(m : ℤ)) / (2 : ℝ)^(-(n : ℤ)) =
        (2 : ℝ)^((n : ℤ) - (m : ℤ)) := by
      rw [div_eq_mul_inv, h_inv]
      rw [← zpow_add₀ (by norm_num)] <;> ring_nf
    rw [h_div]
    have h2 : (n : ℤ) - (m : ℤ) = (k : ℤ) := by
      simp [k, hmn] <;> omega
    rw [h2]
  rw [h_main]
  norm_cast

/-- Component-wise homothety evaluation. -/
lemma homothetyS_apply (s : ℝ) (hs_pos : 0 < s) (i j : ℤ) (x : Plane) :
    (homothetyS s i j x) 0 = (x 0 - (i : ℝ) * s) / s ∧
    (homothetyS s i j x) 1 = (x 1 - (j : ℝ) * s) / s := by
  let lower : Plane := WithLp.toLp (2 : ENNReal)
    (fun k : Fin 2 => if k = 0 then (i : ℝ) * s else (j : ℝ) * s)
  have h1 : (homothetyS s i j x) = (1 / s : ℝ) • (x - lower) := by rfl
  constructor
  · rw [h1]; simp [lower, WithLp.toLp]; field_simp [hs_pos.ne'] <;> ring
  · rw [h1]; simp [lower, WithLp.toLp]; field_simp [hs_pos.ne'] <;> ring

/-- Homothety composition identity. -/
lemma homothety_compose {Δ₁ Δ : ℝ} {i₀ j₀ i' j' : ℤ} {a : ℕ}
    (hΔ₁_pos : 0 < Δ₁) (hΔ_pos : 0 < Δ)
    (ha : Δ₁ / Δ = (a : ℝ)) (x : Plane) :
    homothetyS (Δ / Δ₁) i' j' (homothetyS Δ₁ i₀ j₀ x) =
    homothetyS Δ ((a : ℤ) * i₀ + i') ((a : ℤ) * j₀ + j') x := by
  have h3 : Δ₁ = (a : ℝ) * Δ := by
    field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
  have ha_pos : 0 < (a : ℝ) := by
    have h : (a : ℝ) = Δ₁ / Δ := by field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
    rw [h] <;> positivity
  set I : ℤ := (a : ℤ) * i₀ + i' with hI_def
  set J : ℤ := (a : ℤ) * j₀ + j' with hJ_def
  have hI_cast : (I : ℝ) = (a : ℝ) * (i₀ : ℝ) + (i' : ℝ) := by
    simp [I, hI_def, Int.cast_add, Int.cast_mul] <;> ring
  have hJ_cast : (J : ℝ) = (a : ℝ) * (j₀ : ℝ) + (j' : ℝ) := by
    simp [J, hJ_def, Int.cast_add, Int.cast_mul] <;> ring
  set y := homothetyS Δ₁ i₀ j₀ x with hy_def
  set z := homothetyS (Δ / Δ₁) i' j' y with hz_def
  set w := homothetyS Δ I J x with hw_def
  have h5 := homothetyS_apply (Δ / Δ₁) (by positivity) i' j' y
  have h6 := homothetyS_apply Δ₁ hΔ₁_pos i₀ j₀ x
  have h7 := homothetyS_apply Δ hΔ_pos I J x
  have h0 : z 0 = w 0 := by
    rw [h5.1, h6.1, h7.1, hI_cast, h3]
    field_simp [hΔ_pos.ne', ha_pos.ne'] <;> ring
  have h1 : z 1 = w 1 := by
    rw [h5.2, h6.2, h7.2, hJ_cast, h3]
    field_simp [hΔ_pos.ne', ha_pos.ne'] <;> ring
  have h_eq : z = w := by
    ext i
    fin_cases i <;> tauto
  exact h_eq

/-- dyadicSquare membership gives coordinate inequalities. -/
lemma dyadicSquare_mem {s : ℝ} {i j : ℤ} {p : Plane} (h : p ∈ dyadicSquare s i j) :
    (i : ℝ) * s ≤ p 0 ∧ p 0 < (i + 1 : ℝ) * s ∧
    (j : ℝ) * s ≤ p 1 ∧ p 1 < (j + 1 : ℝ) * s := by
  have h' : p 0 ∈ Set.Ico ((i : ℝ) * s) ((i + 1 : ℝ) * s) ∧
           p 1 ∈ Set.Ico ((j : ℝ) * s) ((j + 1 : ℝ) * s) := by
    simpa [dyadicSquare] using h
  exact ⟨h'.1.1, h'.1.2, h'.2.1, h'.2.2⟩

/-- If P' ⊆ [0,1)² and a dyadic square intersects P', index bounds follow. -/
lemma index_bounds_from_unit {P' : Set Plane} {s : ℝ} {i j : ℤ}
    (hP'_sub : ∀ y ∈ P', 0 ≤ y 0 ∧ y 0 < 1 ∧ 0 ≤ y 1 ∧ y 1 < 1)
    (hs_pos : 0 < s)
    (hnonempty : (P' ∩ dyadicSquare s i j).Nonempty) :
    0 ≤ i ∧ 0 ≤ j ∧ (i : ℝ) < 1 / s ∧ (j : ℝ) < 1 / s := by
  rcases hnonempty with ⟨y, hyP', hyS⟩
  have hb := hP'_sub y hyP'
  have hq := dyadicSquare_mem hyS
  have hi_nonneg : 0 ≤ i := by
    by_contra h
    have h_i_le : i ≤ -1 := by omega
    have h_i1_le : i + 1 ≤ 0 := by omega
    have h9 : (i + 1 : ℝ) * s ≤ 0 := by
      have h10 : (i + 1 : ℝ) ≤ 0 := by exact_mod_cast h_i1_le
      exact mul_nonpos_of_nonpos_of_nonneg h10 (by linarith)
    have h10 : y 0 < (i + 1 : ℝ) * s := hq.2.1
    have h11 : 0 ≤ y 0 := hb.1
    linarith
  have hj_nonneg : 0 ≤ j := by
    by_contra h
    have h_j_le : j ≤ -1 := by omega
    have h_j1_le : j + 1 ≤ 0 := by omega
    have h9 : (j + 1 : ℝ) * s ≤ 0 := by
      have h10 : (j + 1 : ℝ) ≤ 0 := by exact_mod_cast h_j1_le
      exact mul_nonpos_of_nonpos_of_nonneg h10 (by linarith)
    have h10 : y 1 < (j + 1 : ℝ) * s := hq.2.2.2
    have h11 : 0 ≤ y 1 := hb.2.2.1
    linarith
  have hi_lt : (i : ℝ) < 1 / s := by
    have h9 : (i : ℝ) * s ≤ y 0 := hq.1
    have h10 : y 0 < 1 := hb.2.1
    have h11 : (i : ℝ) * s < 1 := by linarith
    have h12 : (i : ℝ) < 1 / s := by
      calc (i : ℝ)
        = ((i : ℝ) * s) / s := by field_simp [hs_pos.ne'] <;> ring
      _ < 1 / s := by gcongr
    exact h12
  have hj_lt : (j : ℝ) < 1 / s := by
    have h9 : (j : ℝ) * s ≤ y 1 := hq.2.2.1
    have h10 : y 1 < 1 := hb.2.2.2
    have h11 : (j : ℝ) * s < 1 := by linarith
    have h12 : (j : ℝ) < 1 / s := by
      calc (j : ℝ)
        = ((j : ℝ) * s) / s := by field_simp [hs_pos.ne'] <;> ring
      _ < 1 / s := by gcongr
    exact h12
  exact ⟨hi_nonneg, hj_nonneg, hi_lt, hj_lt⟩

/-- Dyadic square correspondence under rescaling. -/
lemma dyadicSquare_correspondence {Δ₁ Δ : ℝ} {i₀ j₀ i' j' : ℤ} {a : ℕ}
    (hΔ₁_pos : 0 < Δ₁) (hΔ_pos : 0 < Δ)
    (ha : Δ₁ / Δ = (a : ℝ)) :
    homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') =
      dyadicSquare Δ ((a : ℤ) * i₀ + i') ((a : ℤ) * j₀ + j') := by
  have h3 : Δ₁ = (a : ℝ) * Δ := by
    field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
  have ha_pos : 0 < (a : ℝ) := by
    have h : (a : ℝ) = Δ₁ / Δ := ha.symm
    rw [h] <;> positivity
  set I : ℤ := (a : ℤ) * i₀ + i' with hI_def
  set J : ℤ := (a : ℤ) * j₀ + j' with hJ_def
  ext x
  simp only [Set.mem_preimage, dyadicSquare, Set.mem_setOf_eq]
  let y := homothetyS Δ₁ i₀ j₀ x
  have hy0 : y 0 = (x 0 - (i₀ : ℝ) * Δ₁) / Δ₁ :=
    (homothetyS_apply Δ₁ hΔ₁_pos i₀ j₀ x).1
  have hy1 : y 1 = (x 1 - (j₀ : ℝ) * Δ₁) / Δ₁ :=
    (homothetyS_apply Δ₁ hΔ₁_pos i₀ j₀ x).2
  have hI_cast : (I : ℝ) = (a : ℝ) * (i₀ : ℝ) + (i' : ℝ) := by
    simp [I, hI_def] <;> ring
  have hJ_cast : (J : ℝ) = (a : ℝ) * (j₀ : ℝ) + (j' : ℝ) := by
    simp [J, hJ_def] <;> ring
  have h_iff_i1 : (I : ℝ) * Δ ≤ x 0 ↔
      (i' : ℝ) * (Δ / Δ₁) ≤ (x 0 - (i₀ : ℝ) * Δ₁) / Δ₁ := by
    rw [hI_cast, h3]
    constructor <;> intro h <;> field_simp [hΔ_pos.ne', ha_pos.ne'] at h ⊢ <;> nlinarith
  have h_iff_i2 : x 0 < (I + 1 : ℝ) * Δ ↔
      (x 0 - (i₀ : ℝ) * Δ₁) / Δ₁ < ((i' + 1 : ℝ)) * (Δ / Δ₁) := by
    rw [hI_cast, h3]
    constructor <;> intro h <;> field_simp [hΔ_pos.ne', ha_pos.ne'] at h ⊢ <;> nlinarith
  have h_iff_j1 : (J : ℝ) * Δ ≤ x 1 ↔
      (j' : ℝ) * (Δ / Δ₁) ≤ (x 1 - (j₀ : ℝ) * Δ₁) / Δ₁ := by
    rw [hJ_cast, h3]
    constructor <;> intro h <;> field_simp [hΔ_pos.ne', ha_pos.ne'] at h ⊢ <;> nlinarith
  have h_iff_j2 : x 1 < (J + 1 : ℝ) * Δ ↔
      (x 1 - (j₀ : ℝ) * Δ₁) / Δ₁ < ((j' + 1 : ℝ)) * (Δ / Δ₁) := by
    rw [hJ_cast, h3]
    constructor <;> intro h <;> field_simp [hΔ_pos.ne', ha_pos.ne'] at h ⊢ <;> nlinarith
  constructor
  · intro h
    have hi1 : (i' : ℝ) * (Δ / Δ₁) ≤ y 0 := h.1.1
    have hi2 : y 0 < ((i' + 1 : ℝ)) * (Δ / Δ₁) := h.1.2
    have hj1 : (j' : ℝ) * (Δ / Δ₁) ≤ y 1 := h.2.1
    have hj2 : y 1 < ((j' + 1 : ℝ)) * (Δ / Δ₁) := h.2.2
    rw [hy0] at hi1 hi2; rw [hy1] at hj1 hj2
    simp only [Set.mem_Ico]
    exact ⟨⟨h_iff_i1.mpr hi1, h_iff_i2.mpr hi2⟩, ⟨h_iff_j1.mpr hj1, h_iff_j2.mpr hj2⟩⟩
  · intro h
    have hq := dyadicSquare_mem h
    have hi1 : (I : ℝ) * Δ ≤ x 0 := hq.1
    have hi2 : x 0 < (I + 1 : ℝ) * Δ := hq.2.1
    have hj1 : (J : ℝ) * Δ ≤ x 1 := hq.2.2.1
    have hj2 : x 1 < (J + 1 : ℝ) * Δ := hq.2.2.2
    simp only [Set.mem_Ico]
    rw [hy0, hy1]
    exact ⟨⟨h_iff_i1.mp hi1, h_iff_i2.mp hi2⟩, ⟨h_iff_j1.mp hj1, h_iff_j2.mp hj2⟩⟩

/-- Rescaling of IsRegularBetweenScales. -/
lemma regular_between_scales_rescale
    {P : Set Plane} {δ Δ Δ₁ t C K : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ₁_pos : 0 < Δ₁)
    (hΔ_le_Δ₁ : Δ ≤ Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales) (hΔ_dyadic : Δ ∈ dyadicScales)
    (h : IsRegularBetweenScales P δ Δ t C K)
    (i₀ j₀ : ℤ) :
    IsRegularBetweenScales
      (homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀))
      (δ / Δ₁) (Δ / Δ₁) t C K := by
  rcases dyadicScales_ratio_nat hΔ₁_dyadic hΔ_dyadic hΔ_le_Δ₁ with ⟨a, ha⟩
  set P' : Set Plane := homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀) with hP'_def
  have ha_ge_one : (a : ℝ) ≥ 1 := by
    have h : (a : ℝ) = Δ₁ / Δ := ha.symm
    rw [h]
    exact (one_le_div hΔ_pos).mpr hΔ_le_Δ₁
  have ha_pos : 0 < (a : ℝ) := by linarith
  have hP'_sub : ∀ y ∈ P', 0 ≤ y 0 ∧ y 0 < 1 ∧ 0 ≤ y 1 ∧ y 1 < 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxQ := dyadicSquare_mem hx.2
    have h1 := homothetyS_apply Δ₁ hΔ₁_pos i₀ j₀ x
    have h_y0_nonneg : 0 ≤ (homothetyS Δ₁ i₀ j₀ x) 0 := by
      rw [h1.1]; apply div_nonneg <;> linarith [hxQ.1]
    have h_y0_lt : (homothetyS Δ₁ i₀ j₀ x) 0 < 1 := by
      rw [h1.1]; rw [div_lt_one hΔ₁_pos] <;> linarith [hxQ.2.1]
    have h_y1_nonneg : 0 ≤ (homothetyS Δ₁ i₀ j₀ x) 1 := by
      rw [h1.2]; apply div_nonneg <;> linarith [hxQ.2.2.1]
    have h_y1_lt : (homothetyS Δ₁ i₀ j₀ x) 1 < 1 := by
      rw [h1.2]; rw [div_lt_one hΔ₁_pos] <;> linarith [hxQ.2.2.2]
    exact ⟨h_y0_nonneg, h_y0_lt, h_y1_nonneg, h_y1_lt⟩
  have h_fineδ_pos : 0 < δ / Δ₁ := div_pos hδ_pos hΔ₁_pos
  have h_fineΔ_pos : 0 < Δ / Δ₁ := div_pos hΔ_pos hΔ₁_pos
  have h_fineδ_le_fineΔ : δ / Δ₁ ≤ Δ / Δ₁ := by
    have h1 : δ ≤ Δ := h.1.2.2.1
    gcongr
  have hK_pos : 0 < K := h.2.1
  have h_inv : Δ / Δ₁ = 1 / (a : ℝ) := by
    have h3 : Δ₁ = (a : ℝ) * Δ := by
      field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
    rw [h3] <;> field_simp [hΔ_pos.ne'] <;> ring

  have h_bounds : ∀ (i' j' : ℤ), (P' ∩ dyadicSquare (Δ / Δ₁) i' j').Nonempty →
      0 ≤ i' ∧ 0 ≤ j' ∧ (i' : ℝ) < (a : ℝ) ∧ (j' : ℝ) < (a : ℝ) := by
    intro i' j' hnonempty
    have h := index_bounds_from_unit hP'_sub h_fineΔ_pos hnonempty
    have h1 : 0 ≤ i' := h.1
    have h2 : 0 ≤ j' := h.2.1
    have h3 : (i' : ℝ) < 1 / (Δ / Δ₁) := h.2.2.1
    have h4 : (j' : ℝ) < 1 / (Δ / Δ₁) := h.2.2.2
    have h_a_inv : 1 / (Δ / Δ₁) = (a : ℝ) := by
      rw [h_inv]
      field_simp [ha_pos.ne'] <;> ring
    have h5 : (i' : ℝ) < (a : ℝ) := by
      rw [h_a_inv] at h3; exact h3
    have h6 : (j' : ℝ) < (a : ℝ) := by
      rw [h_a_inv] at h4; exact h4
    exact ⟨h1, h2, h5, h6⟩

  have h_main_correspondence : ∀ (i' j' : ℤ), (P' ∩ dyadicSquare (Δ / Δ₁) i' j').Nonempty →
      let I : ℤ := (a : ℤ) * i₀ + i'
      let J : ℤ := (a : ℤ) * j₀ + j'
      (P ∩ dyadicSquare Δ I J).Nonempty ∧
      (homothetyS (Δ / Δ₁) i' j' '' (P' ∩ dyadicSquare (Δ / Δ₁) i' j') =
        homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J)) := by
    intro i' j' hnonempty
    let I : ℤ := (a : ℤ) * i₀ + i'
    let J : ℤ := (a : ℤ) * j₀ + j'
    have hb := h_bounds i' j' hnonempty
    have hi'_nonneg : 0 ≤ (i' : ℝ) := by exact_mod_cast hb.1
    have hj'_nonneg : 0 ≤ (j' : ℝ) := by exact_mod_cast hb.2.1
    have hi'_lt : (i' : ℝ) < (a : ℝ) := hb.2.2.1
    have hj'_lt : (j' : ℝ) < (a : ℝ) := hb.2.2.2
    have hi'_add1_le : (i' : ℝ) + 1 ≤ (a : ℝ) := by
      have h : i' + 1 ≤ (a : ℤ) := by
        have h' : i' < (a : ℤ) := by exact_mod_cast hi'_lt
        omega
      exact_mod_cast h
    have hj'_add1_le : (j' : ℝ) + 1 ≤ (a : ℝ) := by
      have h : j' + 1 ≤ (a : ℤ) := by
        have h' : j' < (a : ℤ) := by exact_mod_cast hj'_lt
        omega
      exact_mod_cast h
    have h3 : Δ₁ = (a : ℝ) * Δ := by
      field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
    have h_sq_eq : homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') =
        dyadicSquare Δ I J :=
      dyadicSquare_correspondence hΔ₁_pos hΔ_pos ha
    have h_orig_nonempty : (P ∩ dyadicSquare Δ I J).Nonempty := by
      rcases hnonempty with ⟨y, hyP', hyS⟩
      rcases hyP' with ⟨x, hx, rfl⟩
      have hxS : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := hyS
      rw [h_sq_eq] at hxS
      exact ⟨x, hx.1, hxS⟩
    have hI_cast : (I : ℝ) = (a : ℝ) * (i₀ : ℝ) + (i' : ℝ) := by simp [I] <;> ring
    have hJ_cast : (J : ℝ) = (a : ℝ) * (j₀ : ℝ) + (j' : ℝ) := by simp [J] <;> ring
    have h_contain : dyadicSquare Δ I J ⊆ dyadicSquare Δ₁ i₀ j₀ := by
      intro z hz
      have hq := dyadicSquare_mem hz
      simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
      have h1 : (i₀ : ℝ) * Δ₁ ≤ (I : ℝ) * Δ := by
        rw [hI_cast, h3] <;> nlinarith [hi'_nonneg]
      have h2 : (I + 1 : ℝ) * Δ ≤ (i₀ + 1 : ℝ) * Δ₁ := by
        rw [hI_cast, h3] <;> nlinarith [hi'_add1_le]
      have h3' : (j₀ : ℝ) * Δ₁ ≤ (J : ℝ) * Δ := by
        rw [hJ_cast, h3] <;> nlinarith [hj'_nonneg]
      have h4 : (J + 1 : ℝ) * Δ ≤ (j₀ + 1 : ℝ) * Δ₁ := by
        rw [hJ_cast, h3] <;> nlinarith [hj'_add1_le]
      have hq1 : (I : ℝ) * Δ ≤ z 0 := hq.1
      have hq2 : z 0 < (I + 1 : ℝ) * Δ := hq.2.1
      have hq3 : (J : ℝ) * Δ ≤ z 1 := hq.2.2.1
      have hq4 : z 1 < (J + 1 : ℝ) * Δ := hq.2.2.2
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have h_image_eq : homothetyS (Δ / Δ₁) i' j' '' (P' ∩ dyadicSquare (Δ / Δ₁) i' j') =
        homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨⟨x, hx, rfl⟩, hyS⟩, rfl⟩
        have hxS : x ∈ dyadicSquare Δ I J := by
          have h : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := hyS
          rw [h_sq_eq] at h; exact h
        refine ⟨x, ⟨hx.1, hxS⟩, ?_⟩
        exact (homothety_compose hΔ₁_pos hΔ_pos ha (i₀ := i₀) (j₀ := j₀) (i' := i') (j' := j') x).symm
      · rintro ⟨x, hx, rfl⟩
        have hxS : x ∈ dyadicSquare Δ I J := hx.2
        have h_inQ : x ∈ dyadicSquare Δ₁ i₀ j₀ := h_contain hxS
        let y := homothetyS Δ₁ i₀ j₀ x
        have hyP' : y ∈ P' := ⟨x, ⟨hx.1, h_inQ⟩, rfl⟩
        have h_preimg : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := by
          rw [h_sq_eq]; exact hxS
        have hyS : y ∈ dyadicSquare (Δ / Δ₁) i' j' := h_preimg
        have h_eq : homothetyS (Δ / Δ₁) i' j' y = homothetyS Δ I J x :=
          homothety_compose hΔ₁_pos hΔ_pos ha (i₀ := i₀) (j₀ := j₀) (i' := i') (j' := j') x
        exact ⟨y, ⟨hyP', hyS⟩, h_eq⟩
    exact ⟨h_orig_nonempty, h_image_eq⟩

  have hratio : (δ / Δ₁) / (Δ / Δ₁) = δ / Δ := by
    field_simp [hΔ₁_pos.ne', hΔ_pos.ne'] <;> ring

  have h_set : IsSetBetweenScales P' (δ / Δ₁) (Δ / Δ₁) t C := by
    refine' ⟨h_fineδ_pos, h_fineΔ_pos, h_fineδ_le_fineΔ, h.1.2.2.2.1, h.1.2.2.2.2.1, _⟩
    intro i' j' hnonempty
    let I : ℤ := (a : ℤ) * i₀ + i'
    let J : ℤ := (a : ℤ) * j₀ + j'
    have hmc := h_main_correspondence i' j' hnonempty
    have h_goal : IsDeltaSSet (δ / Δ) t C (homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J)) :=
      h.1.2.2.2.2.2 I J hmc.1
    rw [hmc.2, hratio]
    exact h_goal

  have h_cover : ∀ (i' j' : ℤ), (P' ∩ dyadicSquare (Δ / Δ₁) i' j').Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt ((δ / Δ₁) / (Δ / Δ₁))).toNNReal
         (homothetyS (Δ / Δ₁) i' j' '' (P' ∩ dyadicSquare (Δ / Δ₁) i' j')) : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow ((δ / Δ₁) / (Δ / Δ₁)) (-t / 2)) := by
    intro i' j' hnonempty
    let I : ℤ := (a : ℤ) * i₀ + i'
    let J : ℤ := (a : ℤ) * j₀ + j'
    have hmc := h_main_correspondence i' j' hnonempty
    rw [hmc.2, hratio]
    exact h.2.2 I J hmc.1

  exact ⟨h_set, hK_pos, h_cover⟩

/-- Weaken the constants in IsRegularBetweenScales. -/
lemma IsRegularBetweenScales.weaken
    {P : Set Plane} {δ Δ s C K C' K' : ℝ}
    (h : IsRegularBetweenScales P δ Δ s C K)
    (hC'_pos : 0 < C') (hC_le : C ≤ C')
    (hK'_pos : 0 < K') (hK_le : K ≤ K') :
    IsRegularBetweenScales P δ Δ s C' K' := by
  have hδ_pos : 0 < δ := h.1.1
  have hΔ_pos : 0 < Δ := h.1.2.1
  have h_set : IsSetBetweenScales P δ Δ s C' := by
    refine' ⟨hδ_pos, hΔ_pos, h.1.2.2.1, h.1.2.2.2.1, hC'_pos, _⟩
    intro i j hnonempty
    have h_orig : IsDeltaSSet (δ / Δ) s C (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) :=
      h.1.2.2.2.2.2 i j hnonempty
    have hC'_pos' : 0 < C' := hC'_pos
    refine' ⟨h_orig.1, h_orig.2.1, hC'_pos', h_orig.2.2.2.1, _⟩
    intro x r hr
    have h4 := h_orig.2.2.2.2 x r hr
    have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC_le
    calc
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber (δ / Δ).toNNReal _) := h4
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber (δ / Δ).toNNReal _) := by gcongr
  have hdiv_pos : 0 < δ / Δ := div_pos hδ_pos hΔ_pos
  have h_cover : ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
         (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) : ENNReal) ≤
        ENNReal.ofReal (K' * Real.rpow (δ / Δ) (-s / 2)) := by
    intro i j hnonempty
    have h_orig := h.2.2 i j hnonempty
    have h_rpow_nonneg : 0 ≤ Real.rpow (δ / Δ) (-s / 2) := Real.rpow_nonneg hdiv_pos.le _
    have h_le : ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2)) ≤
        ENNReal.ofReal (K' * Real.rpow (δ / Δ) (-s / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have h1 : K * Real.rpow (δ / Δ) (-s / 2) ≤ K' * Real.rpow (δ / Δ) (-s / 2) := by
        gcongr <;> linarith
      exact h1
    exact le_trans h_orig h_le
  exact ⟨h_set, hK'_pos, h_cover⟩

/-- Weaken the constant in IsSetBetweenScales. -/
lemma IsSetBetweenScales.weaken
    {P : Set Plane} {δ Δ s C C' : ℝ}
    (h : IsSetBetweenScales P δ Δ s C)
    (hC'_pos : 0 < C') (hC_le : C ≤ C') :
    IsSetBetweenScales P δ Δ s C' := by
  refine' ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hC'_pos, _⟩
  intro i j hnonempty
  have h_orig : IsDeltaSSet (δ / Δ) s C (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) :=
    h.2.2.2.2.2 i j hnonempty
  refine' ⟨h_orig.1, h_orig.2.1, hC'_pos, h_orig.2.2.2.1, _⟩
  intro x r hr
  have h4 := h_orig.2.2.2.2 x r hr
  have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC_le
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (δ / Δ).toNNReal _) := h4
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (δ / Δ).toNNReal _) := by gcongr

/-- Transfer IsRegularBetweenScales to a subset.

    Given `IsRegularBetweenScales P δ Δ s C K` and `IsSetBetweenScales P' δ Δ s C'`
    for `P' ⊆ P`, conclude `IsRegularBetweenScales P' δ Δ s C' K`.

    The half-scale covering bound transfers by monotonicity of
    `externalCoveringNumber` under subset inclusion; no density assumption
    is needed for the covering bound itself. -/
lemma IsRegularBetweenScales.of_subset
    {P P' : Set Plane} {δ Δ s C C' K : ℝ}
    (h_reg : IsRegularBetweenScales P δ Δ s C K)
    (h_sub : P' ⊆ P)
    (h_set : IsSetBetweenScales P' δ Δ s C') :
    IsRegularBetweenScales P' δ Δ s C' K := by
  have hK_pos : 0 < K := h_reg.2.1
  have h_cover : ∀ (i j : ℤ), (P' ∩ dyadicSquare Δ i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
         (homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j)) : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2)) := by
    intro i j hne
    have h_inter_sub : (P' ∩ dyadicSquare Δ i j) ⊆ (P ∩ dyadicSquare Δ i j) :=
      Set.inter_subset_inter_left _ h_sub
    have hne' : (P ∩ dyadicSquare Δ i j).Nonempty := hne.mono h_inter_sub
    have h_img_sub : homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j) ⊆
        homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, h_inter_sub hx, rfl⟩
    have h_orig : (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
          (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2)) := h_reg.2.2 i j hne'
    have h_mono : (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
          (homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j)) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
          (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_img_sub
    exact le_trans h_mono h_orig
  exact ⟨h_set, hK_pos, h_cover⟩

/-- Rescaling of IsSetBetweenScales (weaker version for normal blocks). -/
lemma set_between_scales_rescale
    {P : Set Plane} {δ Δ Δ₁ t C : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hΔ₁_pos : 0 < Δ₁)
    (hΔ_le_Δ₁ : Δ ≤ Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales) (hΔ_dyadic : Δ ∈ dyadicScales)
    (h : IsSetBetweenScales P δ Δ t C)
    (i₀ j₀ : ℤ) :
    IsSetBetweenScales
      (homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀))
      (δ / Δ₁) (Δ / Δ₁) t C := by
  rcases dyadicScales_ratio_nat hΔ₁_dyadic hΔ_dyadic hΔ_le_Δ₁ with ⟨a, ha⟩
  set P' : Set Plane := homothetyS Δ₁ i₀ j₀ '' (P ∩ dyadicSquare Δ₁ i₀ j₀) with hP'_def
  have ha_ge_one : (a : ℝ) ≥ 1 := by
    have h : (a : ℝ) = Δ₁ / Δ := ha.symm
    rw [h]
    exact (one_le_div hΔ_pos).mpr hΔ_le_Δ₁
  have ha_pos : 0 < (a : ℝ) := by linarith
  have hP'_sub : ∀ y ∈ P', 0 ≤ y 0 ∧ y 0 < 1 ∧ 0 ≤ y 1 ∧ y 1 < 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxQ := dyadicSquare_mem hx.2
    have h1 := homothetyS_apply Δ₁ hΔ₁_pos i₀ j₀ x
    rw [h1.1, h1.2]
    have h_i1 : 0 ≤ (x 0 - (i₀ : ℝ) * Δ₁) / Δ₁ := by
      apply div_nonneg <;> linarith [hxQ.1]
    have h_i2 : (x 0 - (i₀ : ℝ) * Δ₁) / Δ₁ < 1 := by
      rw [div_lt_one hΔ₁_pos] <;> linarith [hxQ.2.1]
    have h_j1 : 0 ≤ (x 1 - (j₀ : ℝ) * Δ₁) / Δ₁ := by
      apply div_nonneg <;> linarith [hxQ.2.2.1]
    have h_j2 : (x 1 - (j₀ : ℝ) * Δ₁) / Δ₁ < 1 := by
      rw [div_lt_one hΔ₁_pos] <;> linarith [hxQ.2.2.2]
    exact ⟨h_i1, h_i2, h_j1, h_j2⟩
  have h_fineδ_pos : 0 < δ / Δ₁ := div_pos hδ_pos hΔ₁_pos
  have h_fineΔ_pos : 0 < Δ / Δ₁ := div_pos hΔ_pos hΔ₁_pos
  have h_fineδ_le_fineΔ : δ / Δ₁ ≤ Δ / Δ₁ := by
    have h1 : δ ≤ Δ := h.2.2.1
    gcongr
  have h_inv : Δ / Δ₁ = 1 / (a : ℝ) := by
    have h3 : Δ₁ = (a : ℝ) * Δ := by
      field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
    rw [h3] <;> field_simp [hΔ_pos.ne'] <;> ring
  have h_bounds : ∀ (i' j' : ℤ), (P' ∩ dyadicSquare (Δ / Δ₁) i' j').Nonempty →
      0 ≤ i' ∧ 0 ≤ j' ∧ (i' : ℝ) < (a : ℝ) ∧ (j' : ℝ) < (a : ℝ) := by
    intro i' j' hnonempty
    have h := index_bounds_from_unit hP'_sub h_fineΔ_pos hnonempty
    have h1 : 0 ≤ i' := h.1
    have h2 : 0 ≤ j' := h.2.1
    have h3 : (i' : ℝ) < 1 / (Δ / Δ₁) := h.2.2.1
    have h4 : (j' : ℝ) < 1 / (Δ / Δ₁) := h.2.2.2
    have h_a_inv : 1 / (Δ / Δ₁) = (a : ℝ) := by
      rw [h_inv]
      field_simp [ha_pos.ne'] <;> ring
    have h5 : (i' : ℝ) < (a : ℝ) := by rw [h_a_inv] at h3; exact h3
    have h6 : (j' : ℝ) < (a : ℝ) := by rw [h_a_inv] at h4; exact h4
    exact ⟨h1, h2, h5, h6⟩
  have h_main_correspondence : ∀ (i' j' : ℤ), (P' ∩ dyadicSquare (Δ / Δ₁) i' j').Nonempty →
      let I : ℤ := (a : ℤ) * i₀ + i'
      let J : ℤ := (a : ℤ) * j₀ + j'
      (P ∩ dyadicSquare Δ I J).Nonempty ∧
      (homothetyS (Δ / Δ₁) i' j' '' (P' ∩ dyadicSquare (Δ / Δ₁) i' j') =
        homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J)) := by
    intro i' j' hnonempty
    let I : ℤ := (a : ℤ) * i₀ + i'
    let J : ℤ := (a : ℤ) * j₀ + j'
    have hb := h_bounds i' j' hnonempty
    have hi'_nonneg : 0 ≤ (i' : ℝ) := by exact_mod_cast hb.1
    have hj'_nonneg : 0 ≤ (j' : ℝ) := by exact_mod_cast hb.2.1
    have hi'_lt : (i' : ℝ) < (a : ℝ) := hb.2.2.1
    have hj'_lt : (j' : ℝ) < (a : ℝ) := hb.2.2.2
    have h_i_int : i' + 1 ≤ (a : ℤ) := by
      have h' : i' < (a : ℤ) := by exact_mod_cast hi'_lt
      omega
    have hi'_add1_le : (i' : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h_i_int
    have h_j_int : j' + 1 ≤ (a : ℤ) := by
      have h' : j' < (a : ℤ) := by exact_mod_cast hj'_lt
      omega
    have hj'_add1_le : (j' : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast h_j_int
    have h3 : Δ₁ = (a : ℝ) * Δ := by
      field_simp [hΔ_pos.ne'] at ha ⊢ <;> linarith
    have h_sq_eq : homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') =
        dyadicSquare Δ I J :=
      dyadicSquare_correspondence hΔ₁_pos hΔ_pos ha
    have h_orig_nonempty : (P ∩ dyadicSquare Δ I J).Nonempty := by
      rcases hnonempty with ⟨y, hyP', hyS⟩
      rcases hyP' with ⟨x, hx, rfl⟩
      have hxS : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := hyS
      rw [h_sq_eq] at hxS
      exact ⟨x, hx.1, hxS⟩
    have hI_cast : (I : ℝ) = (a : ℝ) * (i₀ : ℝ) + (i' : ℝ) := by simp [I] <;> ring
    have hJ_cast : (J : ℝ) = (a : ℝ) * (j₀ : ℝ) + (j' : ℝ) := by simp [J] <;> ring
    have h_contain : dyadicSquare Δ I J ⊆ dyadicSquare Δ₁ i₀ j₀ := by
      intro z hz
      have hq := dyadicSquare_mem hz
      simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
      have h1 : (i₀ : ℝ) * Δ₁ ≤ (I : ℝ) * Δ := by rw [hI_cast, h3] <;> nlinarith [hi'_nonneg]
      have h2 : (I + 1 : ℝ) * Δ ≤ (i₀ + 1 : ℝ) * Δ₁ := by rw [hI_cast, h3] <;> nlinarith [hi'_add1_le]
      have h3' : (j₀ : ℝ) * Δ₁ ≤ (J : ℝ) * Δ := by rw [hJ_cast, h3] <;> nlinarith [hj'_nonneg]
      have h4 : (J + 1 : ℝ) * Δ ≤ (j₀ + 1 : ℝ) * Δ₁ := by rw [hJ_cast, h3] <;> nlinarith [hj'_add1_le]
      have hq1 : (I : ℝ) * Δ ≤ z 0 := hq.1
      have hq2 : z 0 < (I + 1 : ℝ) * Δ := hq.2.1
      have hq3 : (J : ℝ) * Δ ≤ z 1 := hq.2.2.1
      have hq4 : z 1 < (J + 1 : ℝ) * Δ := hq.2.2.2
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have h_image_eq : homothetyS (Δ / Δ₁) i' j' '' (P' ∩ dyadicSquare (Δ / Δ₁) i' j') =
        homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨⟨x, hx, rfl⟩, hyS⟩, rfl⟩
        have hxS : x ∈ dyadicSquare Δ I J := by
          have h : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := hyS
          rw [h_sq_eq] at h; exact h
        refine ⟨x, ⟨hx.1, hxS⟩, ?_⟩
        exact (homothety_compose hΔ₁_pos hΔ_pos ha (i₀ := i₀) (j₀ := j₀) (i' := i') (j' := j') x).symm
      · rintro ⟨x, hx, rfl⟩
        have hxS : x ∈ dyadicSquare Δ I J := hx.2
        have h_inQ : x ∈ dyadicSquare Δ₁ i₀ j₀ := h_contain hxS
        let y := homothetyS Δ₁ i₀ j₀ x
        have hyP' : y ∈ P' := ⟨x, ⟨hx.1, h_inQ⟩, rfl⟩
        have h_preimg : x ∈ homothetyS Δ₁ i₀ j₀ ⁻¹' (dyadicSquare (Δ / Δ₁) i' j') := by
          rw [h_sq_eq]; exact hxS
        have hyS : y ∈ dyadicSquare (Δ / Δ₁) i' j' := h_preimg
        have h_eq : homothetyS (Δ / Δ₁) i' j' y = homothetyS Δ I J x :=
          homothety_compose hΔ₁_pos hΔ_pos ha (i₀ := i₀) (j₀ := j₀) (i' := i') (j' := j') x
        exact ⟨y, ⟨hyP', hyS⟩, h_eq⟩
    exact ⟨h_orig_nonempty, h_image_eq⟩
  have hratio : (δ / Δ₁) / (Δ / Δ₁) = δ / Δ := by
    field_simp [hΔ₁_pos.ne', hΔ_pos.ne'] <;> ring
  refine' ⟨h_fineδ_pos, h_fineΔ_pos, h_fineδ_le_fineΔ, h.2.2.2.1, h.2.2.2.2.1, _⟩
  intro i' j' hnonempty
  let I : ℤ := (a : ℤ) * i₀ + i'
  let J : ℤ := (a : ℤ) * j₀ + j'
  have hmc := h_main_correspondence i' j' hnonempty
  have h_goal : IsDeltaSSet (δ / Δ) t C (homothetyS Δ I J '' (P ∩ dyadicSquare Δ I J)) :=
    h.2.2.2.2.2 I J hmc.1
  rw [hmc.2, hratio]
  exact h_goal

/-- From n+1 strictly decreasing dyadic scales Δ_0=1 > ... > Δ_n=dyadicDelta k,
    with Δ_1=dyadicDelta m, we have k - m ≥ n - 1.
    Hence dyadicDelta (k - m) ≤ dyadicDelta (n - 1). -/
lemma dyadic_scale_gap_bound {n : ℕ} {k m : ℕ} (hnm : 1 ≤ n)
    {Δ : Fin (n + 1) → ℝ}
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = dyadicDelta m)
    (hΔ_end : Δ (Fin.last n) = dyadicDelta k)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_strict : ∀ i : Fin n, Δ (Fin.succ i) < Δ i.castSucc) :
    k - m ≥ n - 1 := by
  choose a ha using fun i : Fin (n + 1) => hΔ_dyadic i
  have h_a_strict : ∀ i : Fin n, a i.castSucc < a (Fin.succ i) := by
    intro i
    have h1 : Δ (Fin.succ i) < Δ i.castSucc := hΔ_strict i
    rw [ha (Fin.succ i), ha i.castSucc] at h1
    by_contra h2
    have h3 : a (Fin.succ i) ≤ a i.castSucc := by omega
    have h4 : (2 : ℝ)^(-(a (Fin.succ i) : ℤ)) ≥ (2 : ℝ)^(-(a i.castSucc : ℤ)) := by
      gcongr <;> norm_num
    linarith
  let b : ℕ → ℤ := fun j => if h : j < n + 1 then a ⟨j, h⟩ else 0
  have h_b_strict : ∀ j : ℕ, j < n → b j < b (j + 1) := by
    intro j hj
    have h_jn : j < n + 1 := by omega
    have h_j1n : j + 1 < n + 1 := by omega
    have h_eq1 : b j = a ⟨j, h_jn⟩ := by
      unfold b
      rw [dif_pos h_jn]
    have h_eq2 : b (j + 1) = a ⟨j + 1, h_j1n⟩ := by
      unfold b
      rw [dif_pos h_j1n]
    rw [h_eq1, h_eq2]
    let i : Fin n := ⟨j, hj⟩
    have h : a i.castSucc < a i.succ := h_a_strict i
    have h_cast : i.castSucc = (⟨j, h_jn⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [i, Fin.castSucc]
      <;> omega
    have h_succ : i.succ = (⟨j + 1, h_j1n⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [i, Fin.succ]
      <;> omega
    rw [h_cast, h_succ] at h
    exact_mod_cast h
  have h_gap1 : ∀ (j : ℕ), 1 ≤ j → j ≤ n → b j ≥ b 1 + ((j : ℤ) - 1) := by
    intro j
    induction' j with j ih
    · intro h1 _; omega
    · intro h1j h_j1n
      by_cases h : j = 0
      · subst h; norm_num
      · have h_j_ge1 : 1 ≤ j := by omega
        have h_jn : j ≤ n := by omega
        have h_ih' := ih h_j_ge1 h_jn
        have h_step : b j < b (j + 1) := h_b_strict j (by omega)
        have h_ge1 : b (j + 1) ≥ b j + 1 := by omega
        simp [Nat.cast_add] at * <;> omega
  have h_main : b n ≥ b 1 + ((n : ℤ) - 1) := h_gap1 n (by omega) (by linarith)
  have h1lt : 1 < n + 1 := by omega
  have h_b1 : b 1 = a 1 := by
    have h : b 1 = a ⟨1, h1lt⟩ := by
      unfold b; rw [dif_pos h1lt]
    rw [h]
    have h2 : (⟨1, h1lt⟩ : Fin (n + 1)) = (1 : Fin (n + 1)) := by
      apply Fin.ext
      have h4 : (1 : ℕ) % (n + 1) = 1 := Nat.mod_eq_of_lt h1lt
      simp [h4]
    rw [h2]
  have hnlt : n < n + 1 := by omega
  have h_bn : b n = a (Fin.last n) := by
    have h : b n = a ⟨n, hnlt⟩ := by
      unfold b; rw [dif_pos hnlt]
    rw [h]
    have h2 : (⟨n, hnlt⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp [Fin.last] <;> omega
    rw [h2]
  rw [h_b1, h_bn] at h_main
  have h_a1 : a 1 = (m : ℤ) := by
    have h := ha 1
    rw [hΔ1] at h
    have h' : (m : ℤ) = a 1 := by simpa [dyadicDelta] using h
    exact h'.symm
  have h_an : a (Fin.last n) = (k : ℤ) := by
    have h := ha (Fin.last n)
    rw [hΔ_end] at h
    have h_last : (Fin.last n : ℕ) = n := by simp
    have h' : (k : ℤ) = a (Fin.last n) := by simpa [dyadicDelta, h_last] using h
    exact h'.symm
  have h_final : (a (Fin.last n) : ℤ) ≥ (a 1 : ℤ) + ((n : ℤ) - 1) := h_main
  rw [h_an, h_a1] at h_final
  have h_goal : (k : ℤ) - (m : ℤ) ≥ (n : ℤ) - 1 := by linarith
  have h_kge : k ≥ m := by
    have h_nonneg : (n : ℤ) - 1 ≥ 0 := by omega
    linarith
  exact_mod_cast h_goal

/-! ========================================================================
    Subset transfer for IsSetBetweenScales / IsRegularBetweenScales
    using covering density and subset_growth_condition (OS Lemma 7.2).
    ======================================================================== -/

/-- If `P` is an `(s,C)`-set between scales `δ,Δ`, and `P' ⊆ P` has covering
    density `c` at scale `δ/Δ` after rescaling within each `Δ`-square, then
    `P'` is an `(s,C/c)`-set between scales `δ,Δ`.

    This is the between-scales analogue of `subset_growth_condition`. -/
lemma IsSetBetweenScales.subset_with_density
    {P P' : Set Plane} {δ Δ s C c : ℝ}
    (h : IsSetBetweenScales P δ Δ s C)
    (hsub : P' ⊆ P)
    (hc_pos : 0 < c)
    (hdensity : ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
      ENNReal.ofReal c *
        Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) ≤
      Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j))) :
    IsSetBetweenScales P' δ Δ s (C / c) := by
  have hδ_pos : 0 < δ := h.1
  have hΔ_pos : 0 < Δ := h.2.1
  have hδ_le_Δ : δ ≤ Δ := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have hC_pos : 0 < C := h.2.2.2.2.1
  have hratio_pos : 0 < δ / Δ := div_pos hδ_pos hΔ_pos
  have hC_div_pos : 0 < C / c := by positivity
  refine' ⟨hδ_pos, hΔ_pos, hδ_le_Δ, hs, hC_div_pos, _⟩
  intro i j hnonempty
  have hP_nonempty : (P ∩ dyadicSquare Δ i j).Nonempty :=
    Set.Nonempty.mono (fun z hz => ⟨hsub hz.1, hz.2⟩) hnonempty
  let A := homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)
  let B := homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j)
  have hB_sub : B ⊆ A := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hsub hy.1, hy.2⟩, rfl⟩
  have hB_nonempty : B.Nonempty := hnonempty.image _
  have hA_sset : IsDeltaSSet (δ / Δ) s C A := h.2.2.2.2.2 i j hP_nonempty
  have hcov : ENNReal.ofReal c * Metric.externalCoveringNumber (δ / Δ).toNNReal A ≤
      Metric.externalCoveringNumber (δ / Δ).toNNReal B :=
    hdensity i j hP_nonempty
  have h_growth : ∀ (x : Plane) (r : ℝ), (δ / Δ) ≤ r →
      Metric.externalCoveringNumber (δ / Δ).toNNReal (B ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (C / c) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (δ / Δ).toNNReal B :=
    DiscretisedFurstenbergEstimate.Uniformization.subset_growth_condition
      hratio_pos hC_pos hs hc_pos hA_sset.2.2.2.2 hB_sub hcov
  exact ⟨hB_nonempty, hratio_pos, hC_div_pos, hs, h_growth⟩

/-- If `P` is `(s,C,K)`-regular between scales `δ,Δ`, and `P' ⊆ P` has covering
    density `c` at scale `δ/Δ` after rescaling within each `Δ`-square, then
    `P'` is `(s,C/c,K)`-regular between scales `δ,Δ`.

    The half-scale covering bound is preserved by subset monotonicity. -/
lemma IsRegularBetweenScales.subset_with_density
    {P P' : Set Plane} {δ Δ s C K c : ℝ}
    (h : IsRegularBetweenScales P δ Δ s C K)
    (hsub : P' ⊆ P)
    (hc_pos : 0 < c)
    (hdensity : ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
      ENNReal.ofReal c *
        Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) ≤
      Metric.externalCoveringNumber (δ / Δ).toNNReal
          (homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j))) :
    IsRegularBetweenScales P' δ Δ s (C / c) K := by
  have h_set : IsSetBetweenScales P' δ Δ s (C / c) :=
    IsSetBetweenScales.subset_with_density h.1 hsub hc_pos hdensity
  have hK_pos : 0 < K := h.2.1
  have h_cover : ∀ (i j : ℤ), (P' ∩ dyadicSquare Δ i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
         (homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j)) : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2)) := by
    intro i j hnonempty
    have hP_nonempty : (P ∩ dyadicSquare Δ i j).Nonempty :=
      Set.Nonempty.mono (fun z hz => ⟨hsub hz.1, hz.2⟩) hnonempty
    let A := homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)
    let B := homothetyS Δ i j '' (P' ∩ dyadicSquare Δ i j)
    have hB_sub : B ⊆ A := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨hsub hy.1, hy.2⟩, rfl⟩
    have h3 : (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal B : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal A : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hB_sub
    have h4 := h.2.2 i j hP_nonempty
    exact le_trans h3 h4
  exact ⟨h_set, hK_pos, h_cover⟩

/-! ========================================================================
    Cardinality-to-covering number bounds for unions of dyadic squares.

    For a finset P of δ-dyadic squares with pointSet A:
      cover_δ(A) ≤ |P|          (each square covered by one δ-ball at its center)
      cover_δ(A) ≥ |P| / 9      (3δ-separated center subset via mod-3 pigeonhole)
    ======================================================================== -/

/-- Center of a dyadic square. -/
def dyadicSquareCenter {n : ℕ} (p : DyadicSquare n) : Plane :=
  WithLp.toLp (2 : ENNReal)
    (fun k : Fin 2 => if k = 0 then ((p.i : ℝ) + 1 / 2) * dyadicDelta n
      else ((p.j : ℝ) + 1 / 2) * dyadicDelta n)

@[simp] lemma dyadicSquareCenter_zero {n : ℕ} (p : DyadicSquare n) :
    dyadicSquareCenter p 0 = ((p.i : ℝ) + 1 / 2) * dyadicDelta n :=
  PiLp.toLp_apply (2 : ENNReal) (fun _ : Fin 2 => ℝ) _ 0

@[simp] lemma dyadicSquareCenter_one {n : ℕ} (p : DyadicSquare n) :
    dyadicSquareCenter p 1 = ((p.j : ℝ) + 1 / 2) * dyadicDelta n :=
  PiLp.toLp_apply (2 : ENNReal) (fun _ : Fin 2 => ℝ) _ 1

/-- Euclidean distance dominates each coordinate difference. -/
lemma euclidean_dist_ge_component {x y : Plane} {k : Fin 2} :
    |x k - y k| ≤ dist x y := by
  have h1 : dist x y = ‖x - y‖ := by exact dist_eq_norm x y
  rw [h1]
  have h2 : ‖x - y‖ = Real.sqrt (((x - y) 0)^2 + ((x - y) 1)^2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
  rw [h2]
  have h3 : ((x - y) k)^2 ≤ ((x - y) 0)^2 + ((x - y) 1)^2 := by
    fin_cases k <;> simp [Fin.sum_univ_two] <;> positivity
  have h4 : Real.sqrt (((x - y) k)^2) ≤ Real.sqrt (((x - y) 0)^2 + ((x - y) 1)^2) :=
    Real.sqrt_le_sqrt h3
  have h5 : Real.sqrt (((x - y) k)^2) = |(x - y) k| := by exact Real.sqrt_sq_eq_abs ((x - y).ofLp k)
  rw [h5] at h4
  simpa using h4

/-- The center of a dyadic square lies in the square. -/
lemma dyadicSquareCenter_mem {n : ℕ} (p : DyadicSquare n) :
    dyadicSquareCenter p ∈ p.toSet := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h0 : dyadicSquareCenter p 0 = ((p.i : ℝ) + 1 / 2) * δ := by
    rw [dyadicSquareCenter_zero] <;> rfl
  have h1 : dyadicSquareCenter p 1 = ((p.j : ℝ) + 1 / 2) * δ := by
    rw [dyadicSquareCenter_one] <;> rfl
  dsimp only [DyadicSquare.toSet, Set.mem_setOf_eq]
  rw [h0, h1]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A δ-ball at the center covers the entire δ-square. -/
lemma dyadicSquare_center_ball_cover {n : ℕ} (p : DyadicSquare n) :
    p.toSet ⊆ Metric.closedBall (dyadicSquareCenter p) (dyadicDelta n) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  intro x hx
  have hxi1 : (p.i : ℝ) * δ ≤ x 0 := hx.1
  have hxi2 : x 0 < ((p.i : ℝ) + 1) * δ := hx.2.1
  have hxj1 : (p.j : ℝ) * δ ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((p.j : ℝ) + 1) * δ := hx.2.2.2
  have hc0 : dyadicSquareCenter p 0 = ((p.i : ℝ) + 1 / 2) * δ := by
    rw [dyadicSquareCenter_zero] <;> rfl
  have hc1 : dyadicSquareCenter p 1 = ((p.j : ℝ) + 1 / 2) * δ := by
    rw [dyadicSquareCenter_one] <;> rfl
  have h1 : |x 0 - dyadicSquareCenter p 0| ≤ δ / 2 := by
    have h_a : x 0 - dyadicSquareCenter p 0 = x 0 - ((p.i : ℝ) + 1 / 2) * δ := by rw [hc0]
    rw [h_a, abs_le]
    constructor <;> linarith [hδ_pos]
  have h2 : |x 1 - dyadicSquareCenter p 1| ≤ δ / 2 := by
    have h_a : x 1 - dyadicSquareCenter p 1 = x 1 - ((p.j : ℝ) + 1 / 2) * δ := by rw [hc1]
    rw [h_a, abs_le]
    constructor <;> linarith [hδ_pos]
  have h3 : dist x (dyadicSquareCenter p) < δ := by
    have h4 : dist x (dyadicSquareCenter p) =
        Real.sqrt ((x 0 - dyadicSquareCenter p 0)^2 + (x 1 - dyadicSquareCenter p 1)^2) := by
      have h : dist x (dyadicSquareCenter p) = ‖x - dyadicSquareCenter p‖ := by exact dist_eq_norm x (dyadicSquareCenter p)
      rw [h]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h4]
    have h5 : (x 0 - dyadicSquareCenter p 0)^2 + (x 1 - dyadicSquareCenter p 1)^2 < δ^2 := by
      have h6 : (x 0 - dyadicSquareCenter p 0)^2 ≤ (δ / 2)^2 := by
        nlinarith [abs_le.mp h1]
      have h7 : (x 1 - dyadicSquareCenter p 1)^2 ≤ (δ / 2)^2 := by
        nlinarith [abs_le.mp h2]
      nlinarith [hδ_pos]
    have h8 : Real.sqrt ((x 0 - dyadicSquareCenter p 0)^2 + (x 1 - dyadicSquareCenter p 1)^2) < δ := by
      rw [Real.sqrt_lt] <;> nlinarith
    exact h8
  exact h3.le

/-- Upper bound: covering number at scale δ of a union of N δ-squares is ≤ N. -/
lemma dyadic_union_cover_upper {n : ℕ} (P : Finset (DyadicSquare n)) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ P, (p.toSet : Set Plane)) ≤ (P.card : ℕ∞) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let centers : Set Plane := P.image dyadicSquareCenter
  have hfin : centers.Finite := by exact Finset.finite_toSet (Finset.image dyadicSquareCenter P)
  have hcover : Metric.IsCover δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane)) centers := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_dist : dist x (dyadicSquareCenter p) ≤ δ := dyadicSquare_center_ball_cover p hxp
    have h_edist : edist x (dyadicSquareCenter p) ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
        exact ENNReal.ofNNReal_toNNReal δ
      rw [h_eq]
      exact ENNReal.ofReal_le_ofReal h_dist
    exact ⟨dyadicSquareCenter p,
      by simpa [centers, Finset.mem_image] using ⟨p, hp, rfl⟩, h_edist⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane)) ≤
      centers.encard := Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h2 : centers.encard ≤ (P.card : ℕ∞) := by
    have h3 : centers.encard = ↑((P.image dyadicSquareCenter).card) := by
      exact Set.encard_coe_eq_coe_finsetCard (Finset.image dyadicSquareCenter P)
    rw [h3]
    exact_mod_cast Finset.card_image_le
  exact h1.trans h2

/-- Lower bound: covering number at scale δ of a union of N δ-squares is ≥ N/9.

    Proof: partition squares by (i mod 3, j mod 3). One of 9 classes has
    ≥ N/9 squares. Their centers are 3δ-separated. A closed δ-ball has
    diameter 2δ < 3δ, so it contains at most one such center. -/
lemma dyadic_union_cover_lower {n : ℕ} (P : Finset (DyadicSquare n)) :
    (P.card : ENNReal) / 9 ≤
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ P, (p.toSet : Set Plane)) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_nn : (↑δ.toNNReal : ℝ) = δ := by
    simp [Real.toNNReal_of_nonneg hδ_pos.le] <;> linarith
  let classes : Finset (ℤ × ℤ) := (Finset.Ico 0 3).product (Finset.Ico 0 3)
  let filter_class (ab : ℤ × ℤ) : Finset (DyadicSquare n) :=
    P.filter (fun p => p.i % 3 = ab.1 % 3 ∧ p.j % 3 = ab.2 % 3)
  have h_union : P = classes.biUnion filter_class := by
    ext p
    simp only [Finset.mem_biUnion, classes, Finset.mem_product, Finset.mem_Ico]
    constructor
    · intro hp
      refine ⟨(p.i % 3, p.j % 3), ?_, ?_⟩
      · have h1 : 0 < (3 : ℤ) := by norm_num
        simp [Int.emod_lt_of_pos p.i h1, Int.emod_lt_of_pos p.j h1] <;> omega
      · simp [filter_class, hp] <;> omega
    · rintro ⟨ab, _, hmem⟩
      exact (Finset.mem_filter.mp hmem).1
  have h_sum : P.card ≤ ∑ ab ∈ classes, (filter_class ab).card := by
    rw [h_union]; exact Finset.card_biUnion_le
  have h9 : classes.card = 9 := by
    simp [classes, Finset.card_product, Finset.Ico_self] <;> norm_num
  have h_exists : ∃ ab ∈ classes, (P.card : ℝ) ≤ 9 * ((filter_class ab).card : ℝ) := by
    by_contra h; push Not at h
    have h_sum2 : (∑ ab ∈ classes, (filter_class ab).card : ℝ) < (P.card : ℝ) := by
      calc
        (∑ ab ∈ classes, (filter_class ab).card : ℝ)
          < ∑ ab ∈ classes, (P.card : ℝ) / 9 := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact ⟨(0, 0), by simp [classes, Finset.mem_Ico]⟩
            · intro ab hab
              have hlt : (filter_class ab).card < (P.card : ℝ) / 9 := by
                have h' : 9 * (filter_class ab).card < (P.card : ℝ) := h ab hab
                linarith
              exact hlt
        _ = (P.card : ℝ) := by rw [Finset.sum_const, h9] <;> ring
    have h3 : (∑ ab ∈ classes, (filter_class ab).card : ℝ) ≥ (P.card : ℝ) := by exact_mod_cast h_sum
    linarith
  rcases h_exists with ⟨ab, hab, hcard⟩
  let S : Finset (DyadicSquare n) := filter_class ab
  have hS_card : (P.card : ℝ) ≤ 9 * (S.card : ℝ) := hcard
  have h_center_inj : Function.Injective (dyadicSquareCenter : DyadicSquare n → Plane) := by
    intro p q h
    have h_eq0 : dyadicSquareCenter p 0 = dyadicSquareCenter q 0 := by rw [h]
    have h_eq1 : dyadicSquareCenter p 1 = dyadicSquareCenter q 1 := by rw [h]
    have hpi0 : dyadicSquareCenter p 0 = ((p.i : ℝ) + 1 / 2) * δ := by
      rw [dyadicSquareCenter_zero] <;> rfl
    have hqi0 : dyadicSquareCenter q 0 = ((q.i : ℝ) + 1 / 2) * δ := by
      rw [dyadicSquareCenter_zero] <;> rfl
    have hpi1 : dyadicSquareCenter p 1 = ((p.j : ℝ) + 1 / 2) * δ := by
      rw [dyadicSquareCenter_one] <;> rfl
    have hqi1 : dyadicSquareCenter q 1 = ((q.j : ℝ) + 1 / 2) * δ := by
      rw [dyadicSquareCenter_one] <;> rfl
    have hi : (p.i : ℝ) = (q.i : ℝ) := by
      rw [hpi0, hqi0] at h_eq0
      apply (mul_right_inj' (show (δ : ℝ) ≠ 0 by linarith)).mp
      linarith
    have hj : (p.j : ℝ) = (q.j : ℝ) := by
      rw [hpi1, hqi1] at h_eq1
      apply (mul_right_inj' (show (δ : ℝ) ≠ 0 by linarith)).mp
      linarith
    have hpi' : p.i = q.i := by exact_mod_cast hi
    have hpj' : p.j = q.j := by exact_mod_cast hj
    cases p <;> cases q <;> simp_all
  let centersS : Finset Plane := S.image dyadicSquareCenter
  have h_centers_card : centersS.card = S.card :=
    Finset.card_image_of_injective _ h_center_inj
  have hcenters_sub : (centersS : Set Plane) ⊆ (⋃ p ∈ P, (p.toSet : Set Plane)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    have hpP : p ∈ P := by
      simpa [S, filter_class] using (Finset.mem_filter.mp hp).1
    exact Set.mem_iUnion₂.mpr ⟨p, hpP, dyadicSquareCenter_mem p⟩
  have h_sep : ∀ (p q : DyadicSquare n), p ∈ S → q ∈ S → p ≠ q →
      3 * δ ≤ dist (dyadicSquareCenter p) (dyadicSquareCenter q) := by
    intro p q hp hq hne
    have hpi3 : p.i % 3 = ab.1 % 3 := (Finset.mem_filter.mp hp).2.1
    have hqi3 : q.i % 3 = ab.1 % 3 := (Finset.mem_filter.mp hq).2.1
    have hpj3 : p.j % 3 = ab.2 % 3 := (Finset.mem_filter.mp hp).2.2
    have hqj3 : q.j % 3 = ab.2 % 3 := (Finset.mem_filter.mp hq).2.2
    have h_i3 : 3 ∣ p.i - q.i := by omega
    have h_j3 : 3 ∣ p.j - q.j := by omega
    by_cases h_i : p.i ≠ q.i
    · have h5 : 3 ≤ |p.i - q.i| := by
        rcases h_i3 with ⟨k, hk⟩
        have h_eq : p.i - q.i = 3 * k := by linarith
        have hk_ne_zero : k ≠ 0 := by intro h; rw [h, mul_zero] at h_eq; omega
        rw [h_eq]
        have h_abs : |3 * k| = 3 * |k| := by simp [abs_mul]
        rw [h_abs]
        have h1 : 1 ≤ |k| := Int.one_le_abs hk_ne_zero
        nlinarith
      have h6 : (3 : ℝ) ≤ |(p.i : ℝ) - (q.i : ℝ)| := by exact_mod_cast h5
      have h7 : 3 * δ ≤ |(p.i : ℝ) - (q.i : ℝ)| * δ := by nlinarith
      have h8 : |dyadicSquareCenter p 0 - dyadicSquareCenter q 0| = |(p.i : ℝ) - (q.i : ℝ)| * δ := by
        have h_eq1 : dyadicSquareCenter p 0 = ((p.i : ℝ) + 1 / 2) * δ := by
          rw [dyadicSquareCenter_zero] <;> rfl
        have h_eq2 : dyadicSquareCenter q 0 = ((q.i : ℝ) + 1 / 2) * δ := by
          rw [dyadicSquareCenter_zero] <;> rfl
        rw [h_eq1, h_eq2]
        have h : ((p.i : ℝ) + 1 / 2) * δ - ((q.i : ℝ) + 1 / 2) * δ = ((p.i : ℝ) - (q.i : ℝ)) * δ := by ring
        rw [h, abs_mul, abs_of_pos hδ_pos]
      have h9 : |dyadicSquareCenter p 0 - dyadicSquareCenter q 0| ≤ dist (dyadicSquareCenter p) (dyadicSquareCenter q) :=
        euclidean_dist_ge_component (k := 0)
      rw [h8] at h9
      linarith
    · have h_i_eq : p.i = q.i := by tauto
      have h_j : p.j ≠ q.j := by
        intro h
        have : p = q := by cases p <;> cases q <;> simp_all
        exact hne this
      have h5 : 3 ≤ |p.j - q.j| := by
        rcases h_j3 with ⟨k, hk⟩
        have h_eq : p.j - q.j = 3 * k := by linarith
        have hk_ne_zero : k ≠ 0 := by intro h; rw [h, mul_zero] at h_eq; omega
        rw [h_eq]
        have h_abs : |3 * k| = 3 * |k| := by simp [abs_mul]
        rw [h_abs]
        have h1 : 1 ≤ |k| := Int.one_le_abs hk_ne_zero
        nlinarith
      have h6 : (3 : ℝ) ≤ |(p.j : ℝ) - (q.j : ℝ)| := by exact_mod_cast h5
      have h7 : 3 * δ ≤ |(p.j : ℝ) - (q.j : ℝ)| * δ := by nlinarith
      have h8 : |dyadicSquareCenter p 1 - dyadicSquareCenter q 1| = |(p.j : ℝ) - (q.j : ℝ)| * δ := by
        have h_eq1 : dyadicSquareCenter p 1 = ((p.j : ℝ) + 1 / 2) * δ := by
          rw [dyadicSquareCenter_one] <;> rfl
        have h_eq2 : dyadicSquareCenter q 1 = ((q.j : ℝ) + 1 / 2) * δ := by
          rw [dyadicSquareCenter_one] <;> rfl
        rw [h_eq1, h_eq2]
        have h : ((p.j : ℝ) + 1 / 2) * δ - ((q.j : ℝ) + 1 / 2) * δ = ((p.j : ℝ) - (q.j : ℝ)) * δ := by ring
        rw [h, abs_mul, abs_of_pos hδ_pos]
      have h9 : |dyadicSquareCenter p 1 - dyadicSquareCenter q 1| ≤ dist (dyadicSquareCenter p) (dyadicSquareCenter q) :=
        euclidean_dist_ge_component (k := 1)
      rw [h8] at h9
      linarith
  have h_ball_one : ∀ (c : Plane), (centersS.filter (fun x => x ∈ Metric.closedBall c δ)).card ≤ 1 := by
    intro c
    by_contra h
    have h2 : 2 ≤ (centersS.filter (fun x => x ∈ Metric.closedBall c δ)).card := by omega
    rcases Finset.one_lt_card.mp h2 with ⟨x, hx, y, hy, hxy⟩
    have hx' : x ∈ centersS := (Finset.mem_filter.mp hx).1
    have hy' : y ∈ centersS := (Finset.mem_filter.mp hy).1
    have hxb : x ∈ Metric.closedBall c δ := (Finset.mem_filter.mp hx).2
    have hyb : y ∈ Metric.closedBall c δ := (Finset.mem_filter.mp hy).2
    rcases Finset.mem_image.mp hx' with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hy' with ⟨q, hq, heq⟩
    have hpq : p ≠ q := by
      intro h
      have heq2 : dyadicSquareCenter p = y := by
        have hq' : p = q := h
        rw [hq'] at *; exact heq
      exact hxy heq2
    have hsep := h_sep p q hp hq hpq
    have hdist1 : dist (dyadicSquareCenter p) c ≤ δ := hxb
    have hdist2 : dist c y ≤ δ := by
      have h : dist y c ≤ δ := hyb
      rw [dist_comm] at h
      exact h
    have hdist3 : dist (dyadicSquareCenter p) y ≤ 2 * δ := by
      calc dist (dyadicSquareCenter p) y
        ≤ dist (dyadicSquareCenter p) c + dist c y := dist_triangle _ _ _
      _ ≤ δ + δ := by linarith
      _ = 2 * δ := by ring
    have hdist4 : dist (dyadicSquareCenter p) (dyadicSquareCenter q) ≤ 2 * δ := by
      rw [heq] at *; exact hdist3
    linarith
  have h_main : ∀ (C : Set Plane), Metric.IsCover δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane)) C →
      (centersS.card : ℕ∞) ≤ C.encard := by
    intro C hC
    by_cases hfin : C.Finite
    · let C' := hfin.toFinset
      have hC'_eq : (C' : Set Plane) = C := by exact Set.Finite.coe_toFinset hfin
      have hC' : Metric.IsCover δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane)) (C' : Set Plane) := by
        rw [hC'_eq] <;> exact hC
      have h_exists : ∀ (x : Plane), x ∈ centersS → ∃ (c : Plane), c ∈ C' ∧ x ∈ Metric.closedBall c δ := by
        intro x hx
        have h5 : x ∈ (⋃ c ∈ (C' : Set Plane), Metric.closedBall c (↑δ.toNNReal)) :=
          hC'.subset_iUnion_closedBall (hcenters_sub hx)
        rcases Set.mem_iUnion₂.mp h5 with ⟨c, hc1, hc2⟩
        have h6 : x ∈ Metric.closedBall c δ := by
          rw [hδ_nn] at hc2; exact hc2
        exact ⟨c, hc1, h6⟩
      let g : Plane → Plane := fun x =>
        if h : x ∈ centersS then Classical.choose (h_exists x h) else 0
      have hg1 : ∀ x ∈ centersS, g x ∈ C' := by
        intro x hx
        have h5 : g x = Classical.choose (h_exists x hx) := by
          simp [g, hx]
        rw [h5]
        exact (Classical.choose_spec (h_exists x hx)).1
      have hg2 : ∀ x ∈ centersS, x ∈ Metric.closedBall (g x) δ := by
        intro x hx
        have h5 : g x = Classical.choose (h_exists x hx) := by
          simp [g, hx]
        rw [h5]
        exact (Classical.choose_spec (h_exists x hx)).2
      have h_inj : Set.InjOn g (centersS : Set Plane) := by
        intro x hx y hy hxy
        have h1 : x ∈ Metric.closedBall (g x) δ := hg2 x hx
        have h2 : y ∈ Metric.closedBall (g y) δ := hg2 y hy
        have h2' : y ∈ Metric.closedBall (g x) δ := by
          have h_eq : g y = g x := hxy.symm
          rw [h_eq] at h2
          exact h2
        by_contra hne
        have h3 : x ∈ centersS.filter (fun z => z ∈ Metric.closedBall (g x) δ) :=
          Finset.mem_filter.mpr ⟨hx, h1⟩
        have h4 : y ∈ centersS.filter (fun z => z ∈ Metric.closedBall (g x) δ) :=
          Finset.mem_filter.mpr ⟨hy, h2'⟩
        have h5 : 2 ≤ (centersS.filter (fun z => z ∈ Metric.closedBall (g x) δ)).card :=
          Finset.one_lt_card.mpr ⟨x, h3, y, h4, hne⟩
        have h6 := h_ball_one (g x)
        omega
      have h_img : centersS.image g ⊆ C' := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact hg1 x hx
      have h_card_img : (centersS.image g).card = centersS.card :=
        Finset.card_image_of_injOn h_inj
      have h8 : centersS.card ≤ C'.card := by
        calc centersS.card
          = (centersS.image g).card := h_card_img.symm
        _ ≤ C'.card := Finset.card_le_card h_img
      have h9 : (centersS.card : ℕ∞) ≤ C.encard := by
        have h10 : C.encard = ↑C'.card := by rw [← hC'_eq] <;> simp
        rw [h10]; exact_mod_cast h8
      exact h9
    · have hinf : C.Infinite := Set.not_finite.mp hfin
      have h9 : C.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr hfin
      rw [h9] <;> simp
  have h10 : (centersS.card : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane)) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h9_ne_zero : (9 : ENNReal) ≠ 0 := by norm_num
  have h9_ne_top : (9 : ENNReal) ≠ ⊤ := by norm_num
  have h_inv : (9 : ENNReal) * (9 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h9_ne_zero h9_ne_top
  have h12 : (P.card : ENNReal) ≤ 9 * (S.card : ENNReal) := by exact_mod_cast hS_card
  have h11 : (P.card : ENNReal) / 9 ≤ (S.card : ENNReal) := by
    calc (P.card : ENNReal) / 9
      = (P.card : ENNReal) * (9 : ENNReal)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (9 * (S.card : ENNReal)) * (9 : ENNReal)⁻¹ := mul_le_mul_of_nonneg_right h12 (by positivity)
    _ = (9 : ENNReal) * ((S.card : ENNReal) * (9 : ENNReal)⁻¹) := by rw [mul_assoc]
    _ = (9 : ENNReal) * ((9 : ENNReal)⁻¹ * (S.card : ENNReal)) := by rw [mul_comm (S.card : ENNReal)]
    _ = ((9 : ENNReal) * (9 : ENNReal)⁻¹) * (S.card : ENNReal) := by rw [←mul_assoc]
    _ = 1 * (S.card : ENNReal) := by rw [h_inv]
    _ = (S.card : ENNReal) := by simp
  have h16 : (S.card : ENNReal) = (centersS.card : ENNReal) := by
    exact_mod_cast h_centers_card.symm
  rw [h16] at h11
  have h17 : (centersS.card : ENNReal) ≤ ↑(Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set Plane))) := by
    exact_mod_cast h10
  exact le_trans h11 h17

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
