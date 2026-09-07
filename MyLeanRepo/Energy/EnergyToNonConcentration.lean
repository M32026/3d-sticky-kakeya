module

/-
# Energy → Non-Concentration (FIXED)

Fixed version with both `energy_implies_interval_card_bound` and
`energy_implies_nonconcentration` fully proved.

Key addition: δ-separation hypothesis and covering-number equality bridge.

## Dependencies
- `Basic` — Nreal, IsRealDeltaSet, dyadicCoveringNumber
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory Set ENNReal Bornology Classical Finset

namespace robust_projection

/-- Helper: if `0 ≤ a ≤ r` and `κ > 0`, then
    `(ENNReal.ofReal a)^(-κ) ≥ (ENNReal.ofReal r)^(-κ)`. -/
lemma enreal_neg_rpow_antimono {a r κ : ℝ} (ha_nonneg : 0 ≤ a) (har : a ≤ r)
    (hr_pos : 0 < r) (hκ_pos : 0 < κ) :
    (ENNReal.ofReal a) ^ (-κ) ≥ (ENNReal.ofReal r) ^ (-κ) := by
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal har
  have h2 : (ENNReal.ofReal a) ^ κ ≤ (ENNReal.ofReal r) ^ κ :=
    ENNReal.rpow_le_rpow h1 hκ_pos.le
  have h3 : ((ENNReal.ofReal a) ^ κ)⁻¹ ≥ ((ENNReal.ofReal r) ^ κ)⁻¹ :=
    ENNReal.inv_le_inv.mpr h2
  have h4 : (ENNReal.ofReal a) ^ (-κ) = ((ENNReal.ofReal a) ^ κ)⁻¹ := by exact rpow_neg (ENNReal.ofReal a) κ
  have h5 : (ENNReal.ofReal r) ^ (-κ) = ((ENNReal.ofReal r) ^ κ)⁻¹ := by exact rpow_neg (ENNReal.ofReal r) κ
  rw [h4, h5]; exact h3

/-- Helper: for `a, b : ENNReal`, `a^2 ≤ b^2` implies `a ≤ b`. -/
lemma enreal_sq_le_sq {a b : ENNReal} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_cases ha : a = ⊤
  · rw [ha] at h
    have hb : b = ⊤ := by simpa [top_pow] using h
    rw [ha, hb]
  · by_cases hb : b = ⊤
    · rw [hb] <;> exact le_top
    · have ha' : a ≠ ⊤ := ha
      have hb' : b ≠ ⊤ := hb
      let x := a.toReal
      let y := b.toReal
      have hx : a = ENNReal.ofReal x := by rw [ENNReal.ofReal_toReal ha']
      have hy : b = ENNReal.ofReal y := by rw [ENNReal.ofReal_toReal hb']
      have hx_nonneg : 0 ≤ x := by positivity
      have hy_nonneg : 0 ≤ y := by positivity
      have h2 : x ^ 2 ≤ y ^ 2 := by
        have h3 : a ^ 2 = ENNReal.ofReal (x ^ 2) := by
          rw [hx, ← ENNReal.ofReal_pow hx_nonneg 2]
        have h4 : b ^ 2 = ENNReal.ofReal (y ^ 2) := by
          rw [hy, ← ENNReal.ofReal_pow hy_nonneg 2]
        rw [h3, h4] at h
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
      have h5 : x ≤ y := by nlinarith
      rw [hx, hy]
      exact ENNReal.ofReal_le_ofReal h5

/-- Cardinality version: bounded κ-energy implies any interval `[a,b]` of length `≤ r`
contains at most `√C · |S| · r^{κ/2}` points. -/
lemma energy_implies_interval_card_bound
    {δ κ C r : ℝ} {S : Finset ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hC : 0 < C)
    (hr_pos : 0 < r) (hδ_le_r : δ ≤ r)
    (h_energy : ∑ p ∈ S, ∑ q ∈ S,
        ENNReal.ofReal (max (dist p q) δ) ^ (-κ) ≤
        ENNReal.ofReal (C * (S.card : ℝ)^2))
    {a b : ℝ} (h_len : b - a ≤ r) :
    (S.filter (fun x => x ∈ Set.Icc a b)).card ≤
      Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) := by
  let S_Q := S.filter (fun x => x ∈ Set.Icc a b)
  have h_subset : S_Q ⊆ S := filter_subset _ _
  let f : ℝ → ℝ → ENNReal := fun p q => ENNReal.ofReal (max (dist p q) δ) ^ (-κ)

  have h_nonneg_all : ∀ (p q : ℝ), 0 ≤ f p q := fun _ _ => bot_le

  have h_dist : ∀ p ∈ S_Q, ∀ q ∈ S_Q, max (dist p q) δ ≤ r := by
    intro p hp q hq
    have hpi : p ∈ Set.Icc a b := (Finset.mem_filter.mp hp).2
    have hqi : q ∈ Set.Icc a b := (Finset.mem_filter.mp hq).2
    have h1 : dist p q ≤ b - a := by
      have h2 : |p - q| ≤ b - a := by
        rw [abs_le]
        constructor <;> linarith [hpi.1, hpi.2, hqi.1, hqi.2]
      simpa [Real.dist_eq] using h2
    have h1' : dist p q ≤ r := le_trans h1 h_len
    exact max_le h1' hδ_le_r

  have h_pointwise : ∀ p ∈ S_Q, ∀ q ∈ S_Q, f p q ≥ (ENNReal.ofReal r) ^ (-κ) := by
    intro p hp q hq
    have h3 : 0 ≤ max (dist p q) δ := by positivity
    exact enreal_neg_rpow_antimono h3 (h_dist p hp q hq) hr_pos hκ

  have h_inner : ∀ p ∈ S_Q, ∑ q ∈ S_Q, f p q ≤ ∑ q ∈ S, f p q := by
    intro p _
    have h : ∀ i ∈ S, i ∉ S_Q → 0 ≤ f p i := fun _ _ _ => h_nonneg_all p _
    exact Finset.sum_le_sum_of_subset_of_nonneg h_subset h

  have h_sum_upper : ∑ p ∈ S_Q, ∑ q ∈ S_Q, f p q ≤ ∑ p ∈ S, ∑ q ∈ S, f p q := by
    have h1 : ∑ p ∈ S_Q, ∑ q ∈ S_Q, f p q ≤ ∑ p ∈ S_Q, ∑ q ∈ S, f p q :=
      Finset.sum_le_sum (fun p hp => h_inner p hp)
    have h2 : ∀ i ∈ S, i ∉ S_Q → 0 ≤ ∑ q ∈ S, f i q := fun _ _ _ => Finset.sum_nonneg (fun q _ => h_nonneg_all _ _)
    have h3 : ∑ p ∈ S_Q, ∑ q ∈ S, f p q ≤ ∑ p ∈ S, ∑ q ∈ S, f p q :=
      Finset.sum_le_sum_of_subset_of_nonneg h_subset h2
    exact le_trans h1 h3

  have h_sum_lower : ∑ p ∈ S_Q, ∑ q ∈ S_Q, f p q ≥
      (ENNReal.ofReal r) ^ (-κ) * (S_Q.card : ENNReal) ^ 2 := by
    have h10 : ∑ p ∈ S_Q, ∑ q ∈ S_Q, f p q ≥
        ∑ p ∈ S_Q, ∑ q ∈ S_Q, (ENNReal.ofReal r) ^ (-κ) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => h_pointwise p hp q hq))
    have h11 : ∑ p ∈ S_Q, ∑ q ∈ S_Q, (ENNReal.ofReal r) ^ (-κ) =
        (ENNReal.ofReal r) ^ (-κ) * (S_Q.card : ENNReal) ^ 2 := by
      simp [Finset.sum_const, pow_two] <;> ring
    rw [h11] at h10
    exact h10

  set n : ENNReal := (S_Q.card : ENNReal) with hn
  set N : ENNReal := (S.card : ENNReal) with hN
  set R : ENNReal := ENNReal.ofReal r with hR
  have hR_pos : 0 < R := ENNReal.ofReal_pos.mpr hr_pos
  have hR_ne_zero : R ≠ 0 := hR_pos.ne'
  have hR_ne_top : R ≠ ⊤ := ENNReal.ofReal_ne_top

  have h14 : R ^ (-κ) * n ^ 2 ≤ ENNReal.ofReal (C * (S.card : ℝ)^2) :=
    le_trans h_sum_lower (le_trans h_sum_upper h_energy)

  have hR_add : R ^ κ * R ^ (-κ) = 1 := by
    have h : R ^ (κ + (-κ)) = R ^ κ * R ^ (-κ) :=
      ENNReal.rpow_add (y := κ) (z := -κ) hR_ne_zero hR_ne_top
    have h0 : κ + (-κ) = (0 : ℝ) := by ring
    rw [h0] at h
    rw [ENNReal.rpow_zero] at h
    exact h.symm

  have hC2 : (ENNReal.ofReal (Real.sqrt C)) ^ 2 = ENNReal.ofReal C := by
    have hsq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt (by linarith)
    have h : (ENNReal.ofReal (Real.sqrt C)) ^ 2 = ENNReal.ofReal ((Real.sqrt C) ^ 2) := by
      rw [← ENNReal.ofReal_pow] <;> norm_num
    rw [h, hsq]

  have h_posC : 0 ≤ C := by linarith
  have h20 : ENNReal.ofReal (C * (S.card : ℝ)^2) =
      (ENNReal.ofReal (Real.sqrt C)) ^ 2 * N ^ 2 := by
    calc
      ENNReal.ofReal (C * (S.card : ℝ)^2)
        = ENNReal.ofReal C * ENNReal.ofReal ((S.card : ℝ)^2) := by
          rw [ENNReal.ofReal_mul h_posC]
      _ = (ENNReal.ofReal (Real.sqrt C)) ^ 2 * ENNReal.ofReal ((S.card : ℝ)^2) := by
          rw [hC2]
      _ = (ENNReal.ofReal (Real.sqrt C)) ^ 2 * N ^ 2 := by
          simp [hN, pow_two] <;> ring

  have h15 : n ^ 2 ≤ (ENNReal.ofReal (Real.sqrt C)) ^ 2 * N ^ 2 * R ^ κ := by
    have h16 : R ^ (-κ) * n ^ 2 ≤ ENNReal.ofReal (C * (S.card : ℝ)^2) := h14
    have h17 : R ^ κ * (R ^ (-κ) * n ^ 2) ≤ R ^ κ * ENNReal.ofReal (C * (S.card : ℝ)^2) := by
      gcongr
    have h18 : R ^ κ * (R ^ (-κ) * n ^ 2) = n ^ 2 := by
      rw [← mul_assoc, hR_add, one_mul]
    have h19 : R ^ κ * ENNReal.ofReal (C * (S.card : ℝ)^2) =
        (ENNReal.ofReal (Real.sqrt C)) ^ 2 * N ^ 2 * R ^ κ := by
      rw [h20] <;> ring
    rw [h18] at h17
    rw [h19] at h17
    exact h17

  set C' : ENNReal := ENNReal.ofReal (Real.sqrt C) with hC'
  have hR_pow2 : (R ^ (κ / 2)) ^ 2 = R ^ κ := by
    have h23 : (R ^ (κ / 2)) ^ 2 = R ^ (κ / 2) * R ^ (κ / 2) := by
      simp [pow_two]
    rw [h23]
    have h24 : R ^ (κ / 2) * R ^ (κ / 2) = R ^ (κ / 2 + κ / 2) :=
      (ENNReal.rpow_add (y := κ / 2) (z := κ / 2) hR_ne_zero hR_ne_top).symm
    rw [h24]
    have h25 : κ / 2 + κ / 2 = κ := by ring
    rw [h25]
  have h21 : (C' * N * R ^ (κ / 2)) ^ 2 = C' ^ 2 * N ^ 2 * R ^ κ := by
    calc
      (C' * N * R ^ (κ / 2)) ^ 2
        = C' ^ 2 * N ^ 2 * (R ^ (κ / 2)) ^ 2 := by
          simp [pow_two, mul_assoc, mul_comm, mul_left_comm] <;> ring
      _ = C' ^ 2 * N ^ 2 * R ^ κ := by rw [hR_pow2]
  have h22 : n ^ 2 ≤ (C' * N * R ^ (κ / 2)) ^ 2 := by
    rw [h21]; exact h15
  have h23 : n ≤ C' * N * R ^ (κ / 2) := enreal_sq_le_sq h22
  have hR_pow_real : R ^ (κ / 2) = ENNReal.ofReal (r ^ (κ / 2)) := by
    have h26 : 0 ≤ r := by positivity
    have h265 : 0 ≤ κ / 2 := by linarith
    exact ENNReal.ofReal_rpow_of_nonneg h26 h265
  have h25 : C' * N * R ^ (κ / 2) = ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) := by
    have h26 : 0 ≤ Real.sqrt C := by positivity
    have h27 : 0 ≤ (S.card : ℝ) := by positivity
    have h28 : 0 ≤ r ^ (κ / 2) := by positivity
    have hN_cast : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by norm_cast
    calc
      C' * N * R ^ (κ / 2)
        = ENNReal.ofReal (Real.sqrt C) * (S.card : ENNReal) * ENNReal.ofReal (r ^ (κ / 2)) := by
          rw [hR_pow_real] <;> simp [hC', hN] <;> ring
      _ = ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (r ^ (κ / 2)) := by
          rw [hN_cast] <;> ring
      _ = ENNReal.ofReal (Real.sqrt C) * (ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (r ^ (κ / 2))) := by ring
      _ = ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal ((S.card : ℝ) * r ^ (κ / 2)) := by
          rw [ENNReal.ofReal_mul h27]
      _ = ENNReal.ofReal (Real.sqrt C * ((S.card : ℝ) * r ^ (κ / 2))) := by
          rw [ENNReal.ofReal_mul h26]
      _ = ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) := by ring_nf
  rw [h25] at h23
  have h24 : (S_Q.card : ENNReal) ≤ ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) := h23
  have h31 : (S_Q.card : ℝ) ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) := by
    by_contra h33
    have hX_nonneg : 0 ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) := by positivity
    have h34 : Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) < (S_Q.card : ℝ) := by linarith
    have h35 : 0 < (S_Q.card : ℝ) := by
      calc 0 ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) := hX_nonneg
           _ < (S_Q.card : ℝ) := h34
    have h36 : ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) < ENNReal.ofReal (S_Q.card : ℝ) := by
      exact (ofReal_lt_ofReal_iff_of_nonneg hX_nonneg).mpr h34
    have h24' : ENNReal.ofReal (S_Q.card : ℝ) ≤ ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) := by
      have h_eq : (S_Q.card : ENNReal) = ENNReal.ofReal (S_Q.card : ℝ) := by norm_cast
      rw [h_eq] at h24
      exact h24
    exact not_le.mpr h36 h24'
  exact h31

/-! ## Covering number equality for δ-separated sets -/

/-- For a δ-separated finite set `T` in ℝ, the dyadic covering number at scale δ
equals `T.card`. Each point lies in a distinct δ-cube. -/
lemma covering_number_eq_card_of_separated
    {δ : ℝ} (hδ : 0 < δ) {T : Finset ℝ}
    (h_sep : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q ≥ δ) :
    dyadicCoveringNumber δ (realLineCopy (T : Set ℝ)) = ↑T.card := by
  let e : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
    (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun (_ : Fin 1) => x)
  let P : Set (EuclideanSpace ℝ (Fin 1)) := realLineCopy (T : Set ℝ)
  have hP_eq : P = e '' (T : Set ℝ) := by
    ext x
    simp [P, realLineCopy, e]
    <;> constructor
    · intro hx
      refine ⟨x 0, hx, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨t, ht, rfl⟩
      simpa [e] using ht
  have hP_finite : Set.Finite P := by
    rw [hP_eq]
    exact (T.finite_toSet.image e)
  let f : EuclideanSpace ℝ (Fin 1) → Set (EuclideanSpace ℝ (Fin 1)) :=
    fun x => dyadicCube δ (fun _ : Fin 1 => ⌊x 0 / δ⌋)
  have h1 : ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ f x := by
    intro x
    simp only [f, dyadicCube, Set.mem_setOf_eq]
    intro i
    fin_cases i
    have h2 : x 0 ∈ Set.Ico (δ * (⌊x 0 / δ⌋ : ℝ)) (δ * ((⌊x 0 / δ⌋ : ℝ) + 1)) := by
      have h3 : (⌊x 0 / δ⌋ : ℝ) ≤ x 0 / δ := Int.floor_le (x 0 / δ)
      have h4 : x 0 / δ < (⌊x 0 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x 0 / δ)
      have h5 : δ * (⌊x 0 / δ⌋ : ℝ) ≤ x 0 := by
        calc δ * (⌊x 0 / δ⌋ : ℝ) ≤ δ * (x 0 / δ) := by gcongr
          _ = x 0 := by field_simp [hδ.ne'] <;> ring
      have h6 : x 0 < δ * ((⌊x 0 / δ⌋ : ℝ) + 1) := by
        calc x 0 = δ * (x 0 / δ) := by field_simp [hδ.ne'] <;> ring
          _ < δ * ((⌊x 0 / δ⌋ : ℝ) + 1) := by gcongr
      exact ⟨h5, h6⟩
    exact h2
  have h_unique : ∀ (x : EuclideanSpace ℝ (Fin 1)) (k : Fin 1 → ℤ),
      x ∈ dyadicCube δ k → k = (fun _ : Fin 1 => ⌊x 0 / δ⌋) := by
    intro x k hk
    have h2 : x 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := hk 0
    have h3 : (k 0 : ℝ) ≤ x 0 / δ := by
      have h4 : δ * (k 0 : ℝ) ≤ x 0 := h2.1
      calc (k 0 : ℝ) = (δ * (k 0 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x 0) / δ := by gcongr
    have h4 : x 0 / δ < (k 0 : ℝ) + 1 := by
      have h5 : x 0 < δ * ((k 0 : ℝ) + 1) := h2.2
      calc x 0 / δ < (δ * ((k 0 : ℝ) + 1)) / δ := by gcongr
        _ = (k 0 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
    have h6 : ⌊x 0 / δ⌋ = k 0 := by
      rw [Int.floor_eq_iff]
      exact ⟨h3, h4⟩
    ext i
    fin_cases i
    exact h6.symm
  have h2 : dyadicCubesMeeting δ P = f '' P := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hQ, ⟨x, hxQ, hxP⟩⟩
      rcases hQ with ⟨k, rfl⟩
      have h3 : k = (fun _ : Fin 1 => ⌊x 0 / δ⌋) := h_unique x k hxQ
      rw [h3]
      exact ⟨x, hxP, rfl⟩
    · rintro ⟨x, hxP, rfl⟩
      refine ⟨⟨(fun _ : Fin 1 => ⌊x 0 / δ⌋), rfl⟩, ⟨x, h1 x, hxP⟩⟩
  have h_inj : Set.InjOn f P := by
    intro x hx y hy h_eq
    have h_x_in : x ∈ f x := h1 x
    rw [h_eq] at h_x_in
    have h_both : x ∈ f y ∧ y ∈ f y := ⟨h_x_in, h1 y⟩
    have hx' : x 0 ∈ Set.Ico (δ * (⌊y 0 / δ⌋ : ℝ)) (δ * ((⌊y 0 / δ⌋ : ℝ) + 1)) := h_both.1 0
    have hy' : y 0 ∈ Set.Ico (δ * (⌊y 0 / δ⌋ : ℝ)) (δ * ((⌊y 0 / δ⌋ : ℝ) + 1)) := h_both.2 0
    have hxk1 : δ * (⌊y 0 / δ⌋ : ℝ) ≤ x 0 := hx'.1
    have hxk2 : x 0 < δ * ((⌊y 0 / δ⌋ : ℝ) + 1) := hx'.2
    have hyk1 : δ * (⌊y 0 / δ⌋ : ℝ) ≤ y 0 := hy'.1
    have hyk2 : y 0 < δ * ((⌊y 0 / δ⌋ : ℝ) + 1) := hy'.2
    have h_dist : dist (x 0) (y 0) < δ := by
      have h1 : |x 0 - y 0| < δ := by
        rw [abs_lt]
        constructor <;> linarith
      simpa [Real.dist_eq] using h1
    have hx0 : x 0 ∈ (T : Set ℝ) := by
      simpa [P, realLineCopy] using hx
    have hy0 : y 0 ∈ (T : Set ℝ) := by
      simpa [P, realLineCopy] using hy
    by_cases h : x 0 = y 0
    · ext i
      fin_cases i <;> exact h
    · have h4 : dist (x 0) (y 0) ≥ δ := h_sep (x 0) hx0 (y 0) hy0 h
      linarith
  have h3 : Set.encard (f '' P) = Set.encard P := h_inj.encard_image
  have h_e_inj : Function.Injective e := by
    intro a b h
    have h5 : e a = e b := h
    have h6 : (e a) 0 = (e b) 0 := by rw [h5]
    simpa [e] using h6
  have h4 : Set.encard P = ↑T.card := by
    rw [hP_eq]
    have h5 : Set.encard (e '' (T : Set ℝ)) = Set.encard (T : Set ℝ) :=
      h_e_inj.encard_image (T : Set ℝ)
    rw [h5]
    rw [T.finite_toSet.encard_eq_coe_toFinset_card]
    simp
  rw [dyadicCoveringNumber, h2, h3, h4]

/-- Sub-lemma 4: Bounded energy implies non-concentration.

If a finite δ-separated 1D set `S` has δ-regularized κ-energy `≤ C · |S|²`,
then `S` is a `(δ, κ/2, √C)`-set.

Requires δ-separation so that each point occupies a distinct δ-cube, making
the dyadic covering number equal to the cardinality. -/
lemma energy_implies_nonconcentration
    {δ κ C : ℝ} {S : Finset ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hC : 0 < C)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hκ_le_two : κ ≤ 2)
    (hS_nonempty : S.Nonempty)
    (h_sep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → dist p q ≥ δ)
    (h_energy : ∑ p ∈ S, ∑ q ∈ S, ENNReal.ofReal (max (dist p q) δ) ^ (-κ)
        ≤ ENNReal.ofReal (C * (S.card : ℝ)^2)) :
    IsRealDeltaSet δ (κ / 2) (Real.sqrt C) (S : Set ℝ) := by
  let A : Set ℝ := (S : Set ℝ)
  let P : Set (EuclideanSpace ℝ (Fin 1)) := realLineCopy A
  have h1_bdd : Bornology.IsBounded (S : Set ℝ) :=
    S.finite_toSet.isBounded
  have h1_iff : ∃ (C : ℝ), ∀ (x : ℝ), x ∈ (S : Set ℝ) → ∀ (y : ℝ), y ∈ (S : Set ℝ) → dist x y ≤ C :=
    Metric.isBounded_iff.mp h1_bdd
  rcases h1_iff with ⟨M, hM⟩
  have hP_bdd : Bornology.IsBounded P := by
    have h_goal : ∃ (C : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ P → ∀ (y : EuclideanSpace ℝ (Fin 1)), y ∈ P → dist x y ≤ C := by
      refine ⟨M, fun x hx y hy => ?_⟩
      have hx0 : x 0 ∈ (S : Set ℝ) := by
        have h : x 0 ∈ A := by simpa [P, realLineCopy] using hx
        simpa [A] using h
      have hy0 : y 0 ∈ (S : Set ℝ) := by
        have h : y 0 ∈ A := by simpa [P, realLineCopy] using hy
        simpa [A] using h
      have h : dist x y ≤ M := by
        have h2 : dist x y = dist (x 0) (y 0) := by
          simp [EuclideanSpace.dist_eq, Fin.sum_univ_one] <;> rfl
        rw [h2]
        exact hM (x 0) hx0 (y 0) hy0
      exact h
    exact Metric.isBounded_iff.mpr h_goal
  have hP_nonempty : P.Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    let p : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun (_ : Fin 1) => x)
    refine ⟨p, ?_⟩
    have h_goal : p 0 ∈ A := by
      simpa [p, A] using hx
    simpa [P, realLineCopy] using h_goal
  have h_s_le_one : κ / 2 ≤ 1 := by linarith
  have h_s_nonneg : 0 ≤ κ / 2 := by linarith
  have hC'_pos : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have h_cover_eq : ENat.toENNReal (dyadicCoveringNumber δ P) = (S.card : ENNReal) := by
    have h := covering_number_eq_card_of_separated hδ h_sep
    exact_mod_cast h
  have h_main_bound : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 1))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) ≤
        ENNReal.ofReal (Real.sqrt C) * ENat.toENNReal (dyadicCoveringNumber δ P) *
          ENNReal.ofReal (r ^ (κ / 2)) := by
    intro r Q hr hQ hδr hr1
    rcases hQ with ⟨k, rfl⟩
    let a : ℝ := r * (k 0 : ℝ)
    let b : ℝ := r * ((k 0 : ℝ) + 1)
    have hrb_pos : 0 < r := by
      rcases hr with ⟨n, rfl⟩
      positivity
    have h_len : b - a = r := by
      simp [a, b] <;> ring
    let I : Set ℝ := Set.Ico a b
    let S_Q : Finset ℝ := S.filter (fun x => x ∈ I)
    have h_sep_Q : ∀ p ∈ S_Q, ∀ q ∈ S_Q, p ≠ q → dist p q ≥ δ := by
      intro p hp q hq
      have hp' : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq' : q ∈ S := (Finset.mem_filter.mp hq).1
      exact h_sep p hp' q hq'
    have h_inter_eq : P ∩ dyadicCube r k = realLineCopy ((S_Q : Set ℝ)) := by
      ext x
      simp only [P, realLineCopy, S_Q, I, dyadicCube, Set.mem_inter_iff, Set.mem_setOf_eq,
        Finset.mem_filter]
      <;> constructor <;> intro h <;> aesop <;> tauto
    have h_cover_Q_eq : ENat.toENNReal (dyadicCoveringNumber δ (P ∩ dyadicCube r k)) =
        (S_Q.card : ENNReal) := by
      rw [h_inter_eq]
      have h := covering_number_eq_card_of_separated hδ h_sep_Q
      exact_mod_cast h
    let S_Icc : Finset ℝ := S.filter (fun x => x ∈ Set.Icc a b)
    have hS_Q_sub : S_Q ⊆ S_Icc := by
      intro x hx
      have hxi : x ∈ I := (Finset.mem_filter.mp hx).2
      have h_in_Icc : x ∈ Set.Icc a b := by
        exact ⟨hxi.1, le_of_lt hxi.2⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, h_in_Icc⟩
    have h_card_bound : S_Icc.card ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) :=
      energy_implies_interval_card_bound hδ hκ hC hrb_pos hδr h_energy
        (by rw [h_len])
    have h_card_Q_bound : S_Q.card ≤ S_Icc.card :=
      Finset.card_le_card hS_Q_sub
    have h_final : (S_Q.card : ℝ) ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) :=
      calc (S_Q.card : ℝ) ≤ (S_Icc.card : ℝ) := by exact_mod_cast h_card_Q_bound
        _ ≤ Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2) := h_card_bound
    rw [h_cover_Q_eq, h_cover_eq]
    have h_pos_r : 0 ≤ r ^ (κ / 2) := by positivity
    have h5 : (S_Q.card : ENNReal) ≤
        ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) := by
      have h_eq_cast : (S_Q.card : ENNReal) = ENNReal.ofReal (S_Q.card : ℝ) := by
        norm_cast
      rw [h_eq_cast]
      have h51 : 0 ≤ (S_Q.card : ℝ) := by positivity
      exact ENNReal.ofReal_le_ofReal h_final
    have h6 : ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2)) =
        ENNReal.ofReal (Real.sqrt C) * (S.card : ENNReal) * ENNReal.ofReal (r ^ (κ / 2)) := by
      have h7 : 0 ≤ Real.sqrt C := by positivity
      have h8 : 0 ≤ (S.card : ℝ) := by positivity
      have h9 : 0 ≤ r ^ (κ / 2) := by positivity
      calc
        ENNReal.ofReal (Real.sqrt C * (S.card : ℝ) * r ^ (κ / 2))
          = ENNReal.ofReal (Real.sqrt C * ((S.card : ℝ) * r ^ (κ / 2))) := by ring_nf
        _ = ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal ((S.card : ℝ) * r ^ (κ / 2)) := by
            rw [ENNReal.ofReal_mul h7]
        _ = ENNReal.ofReal (Real.sqrt C) * ((S.card : ENNReal) * ENNReal.ofReal (r ^ (κ / 2))) := by
            rw [ENNReal.ofReal_mul h8] <;> norm_cast <;> ring
        _ = ENNReal.ofReal (Real.sqrt C) * (S.card : ENNReal) * ENNReal.ofReal (r ^ (κ / 2)) := by ring
    rw [h6] at h5
    exact h5
  have h_s_le_one' : κ / 2 ≤ ((1 : ℕ) : ℝ) := by linarith
  have h_main : @IsDeltaSCSet 1 δ (κ / 2) (Real.sqrt C) P :=
    ⟨hP_bdd, hP_nonempty, by norm_num, hδ_dyadic, hδ, h_s_nonneg, h_s_le_one', hC'_pos, h_main_bound⟩
  exact h_main

end robust_projection
