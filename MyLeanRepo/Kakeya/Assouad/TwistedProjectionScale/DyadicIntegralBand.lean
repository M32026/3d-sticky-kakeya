import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.DyadicIntegralBandStatement
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
WZ2 Section 7: after discarding a controlled low-value tail, select one
dyadic band carrying a fixed fraction of a nonnegative integral.
-/

noncomputable section

open MeasureTheory Finset Set

namespace Kakeya.Assouad

/-- The low-value tail `{g < a}` has integral at most `a * μ X`. -/
private lemma low_tail_bound {α : Type} [MeasurableSpace α] {μ : Measure α}
    {g : α → ENNReal} (hg : Measurable g) {X : Set α} (hX : MeasurableSet X)
    (h_support : ∀ x, x ∉ X → g x = 0) {a : ENNReal} :
    ∫⁻ x in {x | g x < a}, g x ∂μ ≤ a * μ X := by
  let L : Set α := {x | g x < a}
  have hL : MeasurableSet L := hg measurableSet_Iio
  have h_decomp : ∫⁻ x in L ∩ X, g x ∂μ + ∫⁻ x in L \ X, g x ∂μ = ∫⁻ x in L, g x ∂μ :=
    lintegral_inter_add_sdiff g L hX
  have h_outside : ∫⁻ x in L \ X, g x ∂μ = 0 := by
    have h1 : ∀ x ∈ L \ X, g x = 0 := by
      intro x hx
      exact h_support x hx.2
    have h2 : ∫⁻ x in L \ X, g x ∂μ ≤ ∫⁻ x in L \ X, (0 : ENNReal) ∂μ :=
      setLIntegral_mono' (hL.diff hX) (fun x hx => (h1 x hx).le)
    simpa using h2
  have h_main : ∫⁻ x in L, g x ∂μ = ∫⁻ x in L ∩ X, g x ∂μ := by
    rw [←h_decomp, h_outside, add_zero]
  rw [h_main]
  have h3 : ∫⁻ x in L ∩ X, g x ∂μ ≤ ∫⁻ x in L ∩ X, a ∂μ :=
    setLIntegral_mono' (hL.inter hX) (fun x hx => le_of_lt hx.1)
  have h4 : ∫⁻ x in L ∩ X, a ∂μ = a * μ (L ∩ X) := setLIntegral_const (L ∩ X) a
  calc
    ∫⁻ x in L ∩ X, g x ∂μ ≤ ∫⁻ x in L ∩ X, a ∂μ := h3
    _ = a * μ (L ∩ X) := h4
    _ ≤ a * μ X := by
      have h5 : μ (L ∩ X) ≤ μ X := measure_mono (by simp)
      gcongr

/-- If `low + high = I` and `2 * low ≤ I`, then `I ≤ 2 * high`. -/
private lemma ennreal_half_integral {I low high : ENNReal} (hI : I ≠ ⊤)
    (h_sum : low + high = I) (h_low : 2 * low ≤ I) : I ≤ 2 * high := by
  have h1 : 2 * I = 2 * low + 2 * high := by
    have h11 : 2 * (low + high) = 2 * low + 2 * high := by rw [mul_add]
    have h12 : 2 * I = 2 * (low + high) := by rw [h_sum]
    rw [h12, h11]
  have h2 : 2 * low + 2 * high ≤ I + 2 * high :=
    add_le_add h_low (le_refl (2 * high))
  have h3 : 2 * I ≤ I + 2 * high := by
    rw [h1]; exact h2
  have h4 : I + I ≤ I + 2 * high := by
    have h5 : 2 * I = I + I := by simp [two_mul]
    rw [h5] at h3; exact h3
  exact (ENNReal.add_le_add_iff_left hI).mp h4

/-- The high-value set `{a ≤ g}` is covered by the `K+1` dyadic value bands. -/
private lemma dyadic_band_cover {α : Type} {g : α → ENNReal} {a b : ENNReal}
    (ha : a ≠ 0) (ha' : a ≠ ⊤) (_hb : b ≠ ⊤)
    (hgb : ∀ x, g x ≤ b) {K : ℕ} (hK : b ≤ a * (2 ^ K : ENNReal)) :
    {x | a ≤ g x} ⊆ ⋃ k ∈ Finset.range (K + 1), dyadicValueBand g a k := by
  intro x hx
  have h1 : a ≤ g x := hx
  have h2 : g x ≤ b := hgb x
  have h3 : g x ≤ a * (2 ^ K : ENNReal) := h2.trans hK
  have h4 : (2 ^ K : ENNReal) < (2 ^ (K + 1) : ENNReal) := by
    have h41 : (2 ^ K : ℕ) < 2 ^ (K + 1) := by
      apply Nat.pow_lt_pow_right <;> norm_num
    exact_mod_cast h41
  have h5 : a * (2 ^ K : ENNReal) < a * (2 ^ (K + 1) : ENNReal) :=
    ENNReal.mul_lt_mul_right ha ha' h4
  have h6 : g x < a * (2 ^ (K + 1) : ENNReal) := h3.trans_lt h5
  have h_exists : ∃ k : ℕ, g x < a * (2 ^ (k + 1) : ENNReal) := ⟨K, h6⟩
  let k : ℕ := Nat.find h_exists
  have hk_spec : g x < a * (2 ^ (k + 1) : ENNReal) := Nat.find_spec h_exists
  have hk_le : k ≤ K := Nat.find_min' h_exists h6
  have hk_mem : k ∈ Finset.range (K + 1) := by
    have h : k < K + 1 := by omega
    simpa [Finset.mem_range] using h
  have h7 : a * (2 ^ k : ENNReal) ≤ g x := by
    by_cases h_k : k = 0
    · simpa [h_k] using h1
    · have h_kpos : 0 < k := Nat.pos_of_ne_zero h_k
      have h_kminus : k - 1 < k := by omega
      have h8 : ¬(g x < a * (2 ^ ((k - 1) + 1) : ENNReal)) :=
        Nat.find_min h_exists h_kminus
      have h9 : (k - 1) + 1 = k := by omega
      rw [h9] at h8
      exact le_of_not_gt h8
  have h10 : x ∈ dyadicValueBand g a k := by
    simp only [dyadicValueBand, Set.mem_setOf_eq]
    exact ⟨h7, hk_spec⟩
  simpa only [Set.mem_iUnion] using ⟨k, hk_mem, h10⟩

theorem dyadic_integral_band :
    DyadicIntegralBandStatement := by
  intro α _ μ g hg X hX hsupport hXfin a b ha_ne_zero ha_ne_top hb_ne_top hg_b K hb_bound htail hI_ne_zero hI_ne_top
  let I := ∫⁻ x, g x ∂μ
  let L : Set α := {x | g x < a}
  let H : Set α := {x | a ≤ g x}
  have hL_meas : MeasurableSet L := hg measurableSet_Iio
  have hH_meas : MeasurableSet H := hg measurableSet_Ici
  have hL_union_H : L ∪ H = Set.univ := by
    ext x
    simp only [L, H, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : a ≤ g x
    · exact Or.inr h
    · exact Or.inl (lt_of_not_ge h)
  have hL_inter_H : Disjoint L H := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [L, H, Set.mem_setOf_eq] at hx1 hx2
    exact not_le.mpr hx1 hx2
  have ha_pos : 0 < a := zero_lt_iff.mpr ha_ne_zero

  -- Step 1: Low tail bound
  have h1 : ∫⁻ x in L, g x ∂μ ≤ a * μ X :=
    low_tail_bound hg hX hsupport

  -- Step 2: High region has at least half the integral
  let l := ∫⁻ x in L, g x ∂μ
  let h := ∫⁻ x in H, g x ∂μ
  have hI_eq : I = l + h := by
    have h21 : ∫⁻ x in (L ∪ H), g x ∂μ = l + h :=
      lintegral_union hH_meas hL_inter_H
    rw [hL_union_H] at h21
    simpa [I, l, h] using h21
  have h2 : I ≤ 2 * h :=
    ennreal_half_integral hI_ne_top hI_eq.symm (by
      calc 2 * l ≤ 2 * (a * μ X) := by gcongr
           _ ≤ I := htail)

  -- Step 3: Bands cover H and are disjoint
  let B := fun k : ℕ => dyadicValueBand g a k
  have hB_meas : ∀ k : ℕ, MeasurableSet (B k) := by
    intro k
    have h_eq : B k = g ⁻¹' (Set.Ico (a * (2 ^ k : ENNReal)) (a * (2 ^ (k + 1) : ENNReal))) := by
      ext x
      simp [B, dyadicValueBand, Set.mem_preimage, Set.mem_Ico]
    rw [h_eq]
    exact hg measurableSet_Ico
  have hB_disj : Set.PairwiseDisjoint (↑(Finset.range (K + 1))) B := by
    intro j hj k hk hjk
    have h_order : j < k ∨ k < j := by omega
    rcases h_order with (h_jk | h_kj)
    · have h : Disjoint (B j) (B k) := by
        rw [Set.disjoint_left]
        intro x hxj hxk
        have h1 : g x < a * (2 ^ (j + 1) : ENNReal) := hxj.2
        have h2 : a * (2 ^ k : ENNReal) ≤ g x := hxk.1
        have h_j1 : j + 1 ≤ k := by omega
        have h_pow : (2 ^ (j + 1) : ENNReal) ≤ (2 ^ k : ENNReal) :=
          pow_le_pow_right₀ (by norm_num) h_j1
        have h3 : a * (2 ^ (j + 1) : ENNReal) ≤ a * (2 ^ k : ENNReal) := by
          exact mul_le_mul_of_nonneg_left h_pow (by positivity)
        exact not_le.mpr h1 (le_trans h3 h2)
      exact h
    · have h : Disjoint (B k) (B j) := by
        rw [Set.disjoint_left]
        intro x hxk hxj
        have h1 : g x < a * (2 ^ (k + 1) : ENNReal) := hxk.2
        have h2 : a * (2 ^ j : ENNReal) ≤ g x := hxj.1
        have h_k1 : k + 1 ≤ j := by omega
        have h_pow : (2 ^ (k + 1) : ENNReal) ≤ (2 ^ j : ENNReal) :=
          pow_le_pow_right₀ (by norm_num) h_k1
        have h3 : a * (2 ^ (k + 1) : ENNReal) ≤ a * (2 ^ j : ENNReal) := by
          exact mul_le_mul_of_nonneg_left h_pow (by positivity)
        exact not_le.mpr h1 (le_trans h3 h2)
      exact Disjoint.symm h
  have hcover : H ⊆ ⋃ k ∈ Finset.range (K + 1), B k :=
    dyadic_band_cover ha_ne_zero ha_ne_top hb_ne_top hg_b hb_bound

  -- Step 4: Sum of band integrals ≥ high region integral
  let U := ⋃ k ∈ Finset.range (K + 1), B k
  let f := fun k : ℕ => ∫⁻ x in B k, g x ∂μ
  have hsum : ∫⁻ x in U, g x ∂μ = ∑ k ∈ Finset.range (K + 1), f k := by
    rw [lintegral_biUnion_finset hB_disj (fun k _ => hB_meas k)]
  have h_restrict : μ.restrict H ≤ μ.restrict U :=
    MeasureTheory.Measure.restrict_mono_set μ hcover
  have h41 : h ≤ ∫⁻ x in U, g x ∂μ := by
    apply lintegral_mono_fn' h_restrict
    intro x; exact le_refl (g x)
  have h4 : h ≤ ∑ k ∈ Finset.range (K + 1), f k := by
    rw [hsum] at h41
    exact h41

  -- Step 5: Pigeonhole
  have h51 : ∃ k ∈ Finset.range (K + 1), ∀ j ∈ Finset.range (K + 1), f j ≤ f k :=
    Finset.exists_max_image (Finset.range (K + 1)) f (by simp)
  rcases h51 with ⟨k, hk_range, hk_max⟩
  have h52 : ∑ j ∈ Finset.range (K + 1), f j ≤ (Finset.range (K + 1)).card • f k :=
    Finset.sum_le_card_nsmul (Finset.range (K + 1)) f (f k) hk_max
  have h53 : (Finset.range (K + 1)).card • f k = ((K + 1 : ENNReal) * f k) := by
    simp [Finset.card_range, nsmul_eq_mul]
  have h54 : ∑ j ∈ Finset.range (K + 1), f j ≤ (K + 1 : ENNReal) * f k := by
    rw [h53] at h52
    exact h52
  have hk_le_K : k ≤ K := by
    simp only [Finset.mem_range] at hk_range; omega
  have h6 : I ≤ 2 * ((K + 1 : ENNReal) * f k) := by
    calc
      I ≤ 2 * h := h2
      _ ≤ 2 * (∑ j ∈ Finset.range (K + 1), f j) := by gcongr
      _ ≤ 2 * ((K + 1 : ENNReal) * f k) := by gcongr

  -- Step 6: Containment in X
  have h7 : B k ⊆ X := by
    intro x hx
    have h8 : a * (2 ^ k : ENNReal) ≤ g x := hx.1
    have h9 : 0 < g x := by
      have h10 : 0 < a * (2 ^ k : ENNReal) := by positivity
      exact lt_of_lt_of_le h10 h8
    by_contra h11
    have h12 : g x = 0 := hsupport x h11
    rw [h12] at h9
    exact lt_irrefl (0 : ENNReal) h9

  have h_final : I ≤ 2 * (K + 1 : ENNReal) * f k := by
    have h_assoc : 2 * ((K + 1 : ENNReal) * f k) = 2 * (K + 1 : ENNReal) * f k := by
      rw [mul_assoc]
    rw [h_assoc] at h6
    exact h6
  refine ⟨k, hk_le_K, hB_meas k, h7, ?_⟩
  simpa [f] using h_final

end Kakeya.Assouad
