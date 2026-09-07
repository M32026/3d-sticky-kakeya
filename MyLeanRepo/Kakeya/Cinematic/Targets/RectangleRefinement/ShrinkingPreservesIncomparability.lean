import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# PYZ Rectangle Refinement — Part 1: Shrinking preserves incomparability

This module proves the first conjunct of `RectangleRefinementStatement`:
given C-incomparable rectangles R, S and their c-centered shrinks R', S',
the shrunk rectangles are 100-incomparable.

## Proof route (contrapositive, auxiliary rectangle trick)

Assume R' ~₁₀₀ S' via U. Define W_R with `function := U.function` and
`interval := R.interval`. Construct U_R with `function := U.function` and an
interval of length `10L` covering `R.interval`. Then R' ~₁₀₀ W_R via U_R, so
`hComparable` gives `|R x - U x| ≤ C_comp · 100³ · δ` on all of `R.interval`.
Symmetrically for S. A thick rectangle V with function U.function then covers
both R and S, showing R ~_C S — a contradiction.

No `close_graph` extension is needed; all hard estimates are delegated to
`ComparableRectanglesStatement`.

## Key dependencies
- `ComparableRectanglesStatement` (hypothesis)
- `enclosing_interval_exists` helper for constructing covering ParameterIntervals

## Whiteprint node
`RectangleRefinement/Shrinking`
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

-- Helper: left endpoint formula
lemma pi_left_eq (I : ParameterInterval) :
    I.left = I.midpoint - I.length / 2 := by
  simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring

lemma pi_right_eq (I : ParameterInterval) :
    I.right = I.midpoint + I.length / 2 := by
  simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring

/-- Construct a ParameterInterval of target length containing [a, b] ⊆ [0,1]. -/
lemma enclosing_interval_exists {a b L_target : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (h_len : b - a ≤ L_target) (hL1 : L_target ≤ 1) :
    ∃ (I : ParameterInterval), I.left ≤ a ∧ b ≤ I.right ∧ I.length = L_target := by
  set a' : ℝ := max 0 (b - L_target) with ha'_def
  set b' : ℝ := a' + L_target with hb'_def
  have ha'_nonneg : 0 ≤ a' := by
    rw [ha'_def] <;> exact le_max_left _ _
  have hb'_le_one : b' ≤ 1 := by
    rw [hb'_def, ha'_def]
    by_cases h : b - L_target ≤ 0
    · rw [max_eq_left h] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith
  have ha'_le_one : a' ≤ 1 := by linarith [ha'_nonneg, hb'_le_one, hb'_def]
  have ha'_le_b' : a' ≤ b' := by rw [hb'_def] <;> linarith
  have ha'_le_a : a' ≤ a := by
    rw [ha'_def]
    by_cases h : b - L_target ≤ 0
    · rw [max_eq_left h] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith
  have hb_le_b' : b ≤ b' := by
    rw [hb'_def, ha'_def]
    by_cases h : b - L_target ≤ 0
    · rw [max_eq_left h] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith
  have h_len' : b' - a' = L_target := by rw [hb'_def] <;> ring
  let I : ParameterInterval :=
    ⟨a', b', ⟨ha'_nonneg, ha'_le_one⟩, ⟨by linarith, hb'_le_one⟩, ha'_le_b'⟩
  exact ⟨I, ha'_le_a, hb_le_b', by simpa [ParameterInterval.length] using h_len'⟩

/-- Part 1: shrinking preserves incomparability. -/
theorem shrinking_preserves_incomparability
    (hComparable : ComparableRectanglesStatement)
    (K D : ℝ) (hK : 1 ≤ K) (hD : 1 ≤ D)
    (c : ℝ) (hc_pos : 0 < c) (hc_lt_one : c < 1) :
    ∃ C : ℝ, 100 ≤ C ∧
      ∀ family : Set C2Function,
        IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
            IsAdmissibleComparisonScale delta t C →
            ∀ R S R' S' : CurvilinearRectangle delta t,
              R.function ∈ family → S.function ∈ family →
              R.IsOverCentralQuarterOf I →
              S.IsOverCentralQuarterOf I →
              R'.IsCenteredShrinkOf R c →
              S'.IsCenteredShrinkOf S c →
              R.AreLambdaIncomparable S family C →
              R'.AreLambdaIncomparable S' family 100 := by
  rcases hComparable K D hK hD with ⟨C_comp, hC_comp_pos, hComp_prop⟩
  let C : ℝ := C_comp * 100^3 + 122
  have hC_ge_100 : 100 ≤ C := by
    dsimp only [C]; have h₁ : 0 < C_comp := hC_comp_pos; nlinarith
  have hC_ge_sqrt : (11 - c)^2 ≤ C := by
    dsimp only [C]; have h₂ : (11 - c)^2 < 121 := by nlinarith
    nlinarith [hC_comp_pos]
  have hC_ge_bound : C_comp * 100^3 + 1 ≤ C := by
    dsimp only [C] <;> linarith
  refine' ⟨C, hC_ge_100, _⟩
  intro family hFamily I hI delta t hdelta hdt ht1 hAdm
  intro R S R' S' hRfam hSfam hRquarter hSquarter hRshrink hSshrink hIncomp

  have ht_pos : 0 < t := by linarith
  let L := Real.sqrt (delta / t)
  have hL_pos : 0 < L := Real.sqrt_pos.mpr (div_pos hdelta ht_pos)
  have hL_nonneg : 0 ≤ L := by positivity
  have hR_len : R.interval.length = L := by simpa [L] using R.interval_length
  have hS_len : S.interval.length = L := by simpa [L] using S.interval_length
  have hR_len' : R.interval.right - R.interval.left = L := by
    simpa [ParameterInterval.length] using hR_len
  have hS_len' : S.interval.right - S.interval.left = L := by
    simpa [ParameterInterval.length] using hS_len

  -- Extract shrink fields
  have hRshrink_fn : R'.function = R.function := hRshrink.1
  have hRshrink_mid : R'.interval.midpoint = R.interval.midpoint := hRshrink.2.1
  have hRshrink_len : R'.interval.length = c * R.interval.length := hRshrink.2.2.1
  have hRshrink_sub : R'.interval.carrier ⊆ R.interval.carrier := hRshrink.2.2.2
  have hSshrink_fn : S'.function = S.function := hSshrink.1
  have hSshrink_mid : S'.interval.midpoint = S.interval.midpoint := hSshrink.2.1
  have hSshrink_len : S'.interval.length = c * S.interval.length := hSshrink.2.2.1
  have hSshrink_sub : S'.interval.carrier ⊆ S.interval.carrier := hSshrink.2.2.2

  -- Contrapositive
  by_contra h
  have hComparable_R'S' : R'.AreLambdaComparable S' family 100 := by
    simpa [CurvilinearRectangle.AreLambdaIncomparable] using h
  rcases hComparable_R'S' with ⟨U, hUfam, hUcover⟩

  -- U has interval length 10L
  have hU_len : U.interval.length = 10 * L := by
    have h1 : U.interval.length = Real.sqrt (100 * delta / t) := U.interval_length
    rw [h1]
    have h3 : Real.sqrt (100 * delta / t) = 10 * L := by
      have h4 : 0 ≤ delta / t := by positivity
      rw [show (100 * delta / t) = 100 * (delta / t) by ring]
      rw [Real.sqrt_mul (by positivity)]
      have h5 : Real.sqrt 100 = 10 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h5] <;> ring
    exact h3
  have h10L_le_one : 10 * L ≤ 1 := by
    have h : U.interval.length ≤ 1 := by
      have h'' : 0 ≤ U.interval.left := U.interval.left_mem.1
      have h''' : U.interval.right ≤ 1 := U.interval.right_mem.2
      simp [ParameterInterval.length] <;> linarith
    rw [hU_len] at h; exact h

  -- Value bound helper from carrier inclusion
  have h_val_from_cover : ∀ (W : CurvilinearRectangle delta t) (V : CurvilinearRectangle (100 * delta) t),
      W.carrier ⊆ V.carrier → ∀ (x : UnitPoint), x ∈ W.interval.carrier → |W.function x - V.function x| ≤ 100 * delta := by
    intro W V hsub x hx
    have h1 : (x, W.function x) ∈ W.carrier := by
      have h2 : |W.function x - W.function x| ≤ delta := by simpa using hdelta.le
      exact ⟨hx, h2⟩
    have h3 := hsub h1
    exact h3.2

  -- Interval inclusion helper
  have h_int_from_cover : ∀ (W : CurvilinearRectangle delta t) (V : CurvilinearRectangle (100 * delta) t),
      W.carrier ⊆ V.carrier → W.interval.carrier ⊆ V.interval.carrier := by
    intro W V hsub x hx
    have h1 : (x, W.function x) ∈ W.carrier := by
      have h2 : |W.function x - W.function x| ≤ delta := by simpa using hdelta.le
      exact ⟨hx, h2⟩
    have h3 := hsub h1
    exact h3.1

  have hR'_interval_sub_U : R'.interval.carrier ⊆ U.interval.carrier :=
    h_int_from_cover R' U (fun x hx => hUcover (Or.inl hx))
  have hS'_interval_sub_U : S'.interval.carrier ⊆ U.interval.carrier :=
    h_int_from_cover S' U (fun x hx => hUcover (Or.inr hx))

  -- ============================================================
  -- Step 1: Bound |R.function - U.function| on R.interval
  -- ============================================================

  let W_R : CurvilinearRectangle delta t :=
    { function := U.function, interval := R.interval, interval_length := hR_len }

  rcases enclosing_interval_exists
      R.interval.left_mem.1 R.interval.right_mem.2 R.interval.left_le_right
      (by linarith [hR_len', hL_nonneg]) h10L_le_one with
    ⟨I_R, hI_R_left, hI_R_right, hI_R_len⟩

  let U_R : CurvilinearRectangle (100 * delta) t :=
    { function := U.function, interval := I_R,
      interval_length := by
        have h : I_R.length = 10 * L := hI_R_len
        rw [h]
        have h3 : Real.sqrt (100 * delta / t) = 10 * L := by
          have h4 : 0 ≤ delta / t := by positivity
          rw [show (100 * delta / t) = 100 * (delta / t) by ring]
          rw [Real.sqrt_mul (by positivity)]
          have h5 : Real.sqrt 100 = 10 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h5] <;> ring
        exact h3.symm }

  have hR'_sub_UR : R'.carrier ⊆ U_R.carrier := by
    intro p hp
    have hx : p.1 ∈ R'.interval.carrier := hp.1
    have h_x_in_R : p.1 ∈ R.interval.carrier := hRshrink_sub hx
    have h_x_in_IR : p.1 ∈ I_R.carrier := by
      have h1 : I_R.left ≤ R.interval.left := hI_R_left
      have h2 : R.interval.right ≤ I_R.right := hI_R_right
      exact ⟨by linarith [h1, h_x_in_R.1], by linarith [h2, h_x_in_R.2]⟩
    have h_val : |p.2 - U.function p.1| ≤ 100 * delta := by
      have h5 : p ∈ U.carrier := hUcover (Or.inl hp)
      exact h5.2
    exact ⟨h_x_in_IR, h_val⟩

  have hWR_sub_UR : W_R.carrier ⊆ U_R.carrier := by
    intro p hp
    have h_x_in_IR : p.1 ∈ I_R.carrier := by
      have h1 : I_R.left ≤ R.interval.left := hI_R_left
      have h2 : R.interval.right ≤ I_R.right := hI_R_right
      exact ⟨by linarith [h1, hp.1.1], by linarith [h2, hp.1.2]⟩
    have h_val : |p.2 - U.function p.1| ≤ 100 * delta := by
      have h : |p.2 - U.function p.1| ≤ delta := hp.2
      linarith [hdelta]
    exact ⟨h_x_in_IR, h_val⟩

  have hComp_R'_WR : R'.AreLambdaComparable W_R family 100 :=
    ⟨U_R, hUfam, Set.union_subset hR'_sub_UR hWR_sub_UR⟩

  have hR'_quarter : R'.IsOverCentralQuarterOf I := by
    intro x hx; exact hRquarter (hRshrink_sub hx)
  have hWR_quarter : W_R.IsOverCentralQuarterOf I := by
    simpa [W_R, CurvilinearRectangle.IsOverCentralQuarterOf] using hRquarter
  have hR'_fam : R'.function ∈ family := by
    rw [hRshrink_fn] <;> exact hRfam

  have hComp_result_R := hComp_prop family hFamily I hI delta t (100 : ℝ)
    hdelta hdt (by norm_num)
    R' W_R hR'_fam hUfam hR'_quarter hWR_quarter hComp_R'_WR

  -- Hull of R' and W_R equals R.interval.carrier
  have hR'_left_ge : R.interval.left ≤ R'.interval.left := by
    let aR' : UnitPoint := ⟨R'.interval.left, R'.interval.left_mem⟩
    have h' : aR' ∈ R'.interval.carrier := by
      exact ⟨by rfl, R'.interval.left_le_right⟩
    have h'' : aR' ∈ R.interval.carrier := hRshrink_sub h'
    exact h''.1
  have hR'_right_le : R'.interval.right ≤ R.interval.right := by
    let bR' : UnitPoint := ⟨R'.interval.right, R'.interval.right_mem⟩
    have h' : bR' ∈ R'.interval.carrier := by
      exact ⟨R'.interval.left_le_right, by rfl⟩
    have h'' : bR' ∈ R.interval.carrier := hRshrink_sub h'
    exact h''.2

  have h_hull_R : R'.intervalHullCarrier W_R = R.interval.carrier := by
    ext x
    simp only [CurvilinearRectangle.intervalHullCarrier, W_R, ParameterInterval.carrier, Set.mem_setOf_eq]
    constructor
    · intro hx
      have h3 : min R'.interval.left R.interval.left = R.interval.left := by
        rw [min_eq_right] <;> exact hR'_left_ge
      have h4 : max R'.interval.right R.interval.right = R.interval.right := by
        rw [max_eq_right] <;> exact hR'_right_le
      rw [h3, h4] at hx <;> exact ⟨hx.1, hx.2⟩
    · intro hx
      have h5 : min R'.interval.left R.interval.left ≤ (x : ℝ) := by
        rw [min_eq_right hR'_left_ge] <;> exact hx.1
      have h6 : (x : ℝ) ≤ max R'.interval.right R.interval.right := by
        rw [max_eq_right hR'_right_le] <;> exact hx.2
      exact ⟨h5, h6⟩

  have hBound_R : ∀ x ∈ R.interval.carrier, |R.function x - U.function x| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta := by
    have h : ∀ x ∈ R'.intervalHullCarrier W_R, |R'.function x - W_R.function x| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta :=
      hComp_result_R.2
    rw [h_hull_R] at h
    intro x hx
    have h_special := h x hx
    have h' : R'.function x = R.function x := by rw [hRshrink_fn]
    have h'' : W_R.function x = U.function x := by rfl
    rw [h', h''] at h_special
    exact h_special

  -- ============================================================
  -- Step 2: Bound |S.function - U.function| on S.interval
  -- ============================================================

  let W_S : CurvilinearRectangle delta t :=
    { function := U.function, interval := S.interval, interval_length := hS_len }

  rcases enclosing_interval_exists
      S.interval.left_mem.1 S.interval.right_mem.2 S.interval.left_le_right
      (by linarith [hS_len', hL_nonneg]) h10L_le_one with
    ⟨I_S, hI_S_left, hI_S_right, hI_S_len⟩

  let U_S : CurvilinearRectangle (100 * delta) t :=
    { function := U.function, interval := I_S,
      interval_length := by
        have h : I_S.length = 10 * L := hI_S_len
        rw [h]
        have h3 : Real.sqrt (100 * delta / t) = 10 * L := by
          have h4 : 0 ≤ delta / t := by positivity
          rw [show (100 * delta / t) = 100 * (delta / t) by ring]
          rw [Real.sqrt_mul (by positivity)]
          have h5 : Real.sqrt 100 = 10 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h5] <;> ring
        exact h3.symm }

  have hS'_sub_US : S'.carrier ⊆ U_S.carrier := by
    intro p hp
    have hx : p.1 ∈ S'.interval.carrier := hp.1
    have h_x_in_S : p.1 ∈ S.interval.carrier := hSshrink_sub hx
    have h_x_in_IS : p.1 ∈ I_S.carrier := by
      have h1 : I_S.left ≤ S.interval.left := hI_S_left
      have h2 : S.interval.right ≤ I_S.right := hI_S_right
      exact ⟨by linarith [h1, h_x_in_S.1], by linarith [h2, h_x_in_S.2]⟩
    have h_val : |p.2 - U.function p.1| ≤ 100 * delta := by
      have h5 : p ∈ U.carrier := hUcover (Or.inr hp)
      exact h5.2
    exact ⟨h_x_in_IS, h_val⟩

  have hWS_sub_US : W_S.carrier ⊆ U_S.carrier := by
    intro p hp
    have h_x_in_IS : p.1 ∈ I_S.carrier := by
      have h1 : I_S.left ≤ S.interval.left := hI_S_left
      have h2 : S.interval.right ≤ I_S.right := hI_S_right
      exact ⟨by linarith [h1, hp.1.1], by linarith [h2, hp.1.2]⟩
    have h_val : |p.2 - U.function p.1| ≤ 100 * delta := by
      have h : |p.2 - U.function p.1| ≤ delta := hp.2
      linarith [hdelta]
    exact ⟨h_x_in_IS, h_val⟩

  have hComp_S'_WS : S'.AreLambdaComparable W_S family 100 :=
    ⟨U_S, hUfam, Set.union_subset hS'_sub_US hWS_sub_US⟩

  have hS'_quarter : S'.IsOverCentralQuarterOf I := by
    intro x hx; exact hSquarter (hSshrink_sub hx)
  have hWS_quarter : W_S.IsOverCentralQuarterOf I := by
    simpa [W_S, CurvilinearRectangle.IsOverCentralQuarterOf] using hSquarter
  have hS'_fam : S'.function ∈ family := by
    rw [hSshrink_fn] <;> exact hSfam

  have hComp_result_S := hComp_prop family hFamily I hI delta t (100 : ℝ)
    hdelta hdt (by norm_num)
    S' W_S hS'_fam hUfam hS'_quarter hWS_quarter hComp_S'_WS

  have hS'_left_ge : S.interval.left ≤ S'.interval.left := by
    let aS' : UnitPoint := ⟨S'.interval.left, S'.interval.left_mem⟩
    have h' : aS' ∈ S'.interval.carrier := by
      exact ⟨by rfl, S'.interval.left_le_right⟩
    have h'' : aS' ∈ S.interval.carrier := hSshrink_sub h'
    exact h''.1
  have hS'_right_le : S'.interval.right ≤ S.interval.right := by
    let bS' : UnitPoint := ⟨S'.interval.right, S'.interval.right_mem⟩
    have h' : bS' ∈ S'.interval.carrier := by
      exact ⟨S'.interval.left_le_right, by rfl⟩
    have h'' : bS' ∈ S.interval.carrier := hSshrink_sub h'
    exact h''.2

  have h_hull_S : S'.intervalHullCarrier W_S = S.interval.carrier := by
    ext x
    simp only [CurvilinearRectangle.intervalHullCarrier, W_S, ParameterInterval.carrier, Set.mem_setOf_eq]
    constructor
    · intro hx
      have h3 : min S'.interval.left S.interval.left = S.interval.left := by
        rw [min_eq_right] <;> exact hS'_left_ge
      have h4 : max S'.interval.right S.interval.right = S.interval.right := by
        rw [max_eq_right] <;> exact hS'_right_le
      rw [h3, h4] at hx <;> exact ⟨hx.1, hx.2⟩
    · intro hx
      have h5 : min S'.interval.left S.interval.left ≤ (x : ℝ) := by
        rw [min_eq_right hS'_left_ge] <;> exact hx.1
      have h6 : (x : ℝ) ≤ max S'.interval.right S.interval.right := by
        rw [max_eq_right hS'_right_le] <;> exact hx.2
      exact ⟨h5, h6⟩

  have hBound_S : ∀ x ∈ S.interval.carrier, |S.function x - U.function x| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta := by
    have h : ∀ x ∈ S'.intervalHullCarrier W_S, |S'.function x - W_S.function x| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta :=
      hComp_result_S.2
    rw [h_hull_S] at h
    intro x hx
    have h_special := h x hx
    have h' : S'.function x = S.function x := by rw [hSshrink_fn]
    have h'' : W_S.function x = U.function x := by rfl
    rw [h', h''] at h_special
    exact h_special

  -- ============================================================
  -- Step 3: Hull length bound for R and S
  -- ============================================================

  have hR'_in_U_left : U.interval.left ≤ R'.interval.left := by
    let aR' : UnitPoint := ⟨R'.interval.left, R'.interval.left_mem⟩
    have h' : aR' ∈ R'.interval.carrier := by exact ⟨by rfl, R'.interval.left_le_right⟩
    have h'' := hR'_interval_sub_U h'
    exact h''.1
  have hR'_in_U_right : R'.interval.right ≤ U.interval.right := by
    let bR' : UnitPoint := ⟨R'.interval.right, R'.interval.right_mem⟩
    have h' : bR' ∈ R'.interval.carrier := by exact ⟨R'.interval.left_le_right, by rfl⟩
    have h'' := hR'_interval_sub_U h'
    exact h''.2
  have hS'_in_U_left : U.interval.left ≤ S'.interval.left := by
    let aS' : UnitPoint := ⟨S'.interval.left, S'.interval.left_mem⟩
    have h' : aS' ∈ S'.interval.carrier := by exact ⟨by rfl, S'.interval.left_le_right⟩
    have h'' := hS'_interval_sub_U h'
    exact h''.1
  have hS'_in_U_right : S'.interval.right ≤ U.interval.right := by
    let bS' : UnitPoint := ⟨S'.interval.right, S'.interval.right_mem⟩
    have h' : bS' ∈ S'.interval.carrier := by exact ⟨S'.interval.left_le_right, by rfl⟩
    have h'' := hS'_interval_sub_U h'
    exact h''.2

  let hL' := min R'.interval.left S'.interval.left
  let hR' := max R'.interval.right S'.interval.right
  have h_hull_R'S'_len : hR' - hL' ≤ 10 * L := by
    have h1 : U.interval.left ≤ hL' := by
      simp only [hL']
      exact le_min hR'_in_U_left hS'_in_U_left
    have h2 : hR' ≤ U.interval.right := by
      simp only [hR']
      exact max_le hR'_in_U_right hS'_in_U_right
    have h3 : hR' - hL' ≤ U.interval.right - U.interval.left := by linarith
    have h4 : U.interval.right - U.interval.left = U.interval.length := by
      simp [ParameterInterval.length] <;> ring
    rw [h4] at h3
    rw [hU_len] at h3
    exact h3

  -- Midpoint extensions
  have hR_left_ext : R.interval.left = R'.interval.left - (1 - c) * L / 2 := by
    rw [pi_left_eq R.interval, pi_left_eq R'.interval]
    rw [hRshrink_mid, hRshrink_len, hR_len] <;> ring
  have hR_right_ext : R.interval.right = R'.interval.right + (1 - c) * L / 2 := by
    rw [pi_right_eq R.interval, pi_right_eq R'.interval]
    rw [hRshrink_mid, hRshrink_len, hR_len] <;> ring
  have hS_left_ext : S.interval.left = S'.interval.left - (1 - c) * L / 2 := by
    rw [pi_left_eq S.interval, pi_left_eq S'.interval]
    rw [hSshrink_mid, hSshrink_len, hS_len] <;> ring
  have hS_right_ext : S.interval.right = S'.interval.right + (1 - c) * L / 2 := by
    rw [pi_right_eq S.interval, pi_right_eq S'.interval]
    rw [hSshrink_mid, hSshrink_len, hS_len] <;> ring

  let hL := min R.interval.left S.interval.left
  let hR := max R.interval.right S.interval.right

  have h_hull_RS_len : hR - hL ≤ (11 - c) * L := by
    have h1 : hL = hL' - (1 - c) * L / 2 := by
      simp only [hL, hL']
      rw [hR_left_ext, hS_left_ext]
      by_cases h : R'.interval.left ≤ S'.interval.left
      · have h' : R'.interval.left - (1 - c) * L / 2 ≤ S'.interval.left - (1 - c) * L / 2 := by linarith
        rw [min_eq_left h', min_eq_left h] <;> ring
      · have h' : S'.interval.left - (1 - c) * L / 2 < R'.interval.left - (1 - c) * L / 2 := by linarith
        rw [min_eq_right (by linarith), min_eq_right (by linarith)] <;> ring
    have h2 : hR = hR' + (1 - c) * L / 2 := by
      simp only [hR, hR']
      rw [hR_right_ext, hS_right_ext]
      by_cases h : R'.interval.right ≤ S'.interval.right
      · have h' : R'.interval.right + (1 - c) * L / 2 ≤ S'.interval.right + (1 - c) * L / 2 := by linarith
        rw [max_eq_right h', max_eq_right h] <;> ring
      · have h' : S'.interval.right + (1 - c) * L / 2 < R'.interval.right + (1 - c) * L / 2 := by linarith
        rw [max_eq_left (by linarith), max_eq_left (by linarith)] <;> ring
    have h3 : hR - hL = hR' - hL' + (1 - c) * L := by
      rw [h1, h2] <;> ring
    have h4 : hR' - hL' ≤ 10 * L := h_hull_R'S'_len
    have h5 : hR - hL ≤ (11 - c) * L := by
      rw [h3] <;> linarith
    exact h5

  -- ============================================================
  -- Step 4: Construct V covering R and S
  -- ============================================================

  have hsqrtC : Real.sqrt C ≥ 11 - c := by
    have h1 : 0 ≤ 11 - c := by linarith
    have h2 : (11 - c)^2 ≤ C := hC_ge_sqrt
    have h3 : Real.sqrt ((11 - c)^2) = 11 - c := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h1]
    have h4 : Real.sqrt ((11 - c)^2) ≤ Real.sqrt C := Real.sqrt_le_sqrt h2
    rw [h3] at h4; exact h4

  have hCL_le_one : Real.sqrt C * L ≤ 1 := by
    have hAdm' : C * delta ≤ t := hAdm.2
    have h5 : C * delta / t ≤ 1 := by
      calc C * delta / t ≤ t / t := by gcongr
        _ = 1 := by field_simp [ht_pos.ne'] <;> linarith
    have h6 : Real.sqrt (C * delta / t) ≤ 1 := by
      rw [Real.sqrt_le_one] <;> linarith
    have h7 : Real.sqrt (C * delta / t) = Real.sqrt C * L := by
      have h8 : 0 ≤ C := by linarith
      rw [show C * delta / t = C * (delta / t) by ring]
      rw [Real.sqrt_mul h8] <;> rfl
    rw [h7] at h6; exact h6

  have hL_nonneg' : 0 ≤ hL := by
    have h1 : 0 ≤ R.interval.left := R.interval.left_mem.1
    have h2 : 0 ≤ S.interval.left := S.interval.left_mem.1
    exact le_min h1 h2
  have hR_le_one : hR ≤ 1 := by
    have h1 : R.interval.right ≤ 1 := R.interval.right_mem.2
    have h2 : S.interval.right ≤ 1 := S.interval.right_mem.2
    exact max_le h1 h2
  have hL_le_hR : hL ≤ hR := by
    have h3 : hL ≤ R.interval.left := min_le_left _ _
    have h4 : R.interval.left ≤ R.interval.right := R.interval.left_le_right
    have h5 : R.interval.right ≤ hR := le_max_left _ _
    exact le_trans h3 (le_trans h4 h5)

  rcases enclosing_interval_exists hL_nonneg' hR_le_one hL_le_hR
      (show hR - hL ≤ Real.sqrt C * L from by
        have h : hR - hL ≤ (11 - c) * L := h_hull_RS_len
        have h' : (11 - c) * L ≤ Real.sqrt C * L := by
          gcongr <;> linarith
        linarith)
      hCL_le_one with
    ⟨I_V, hI_V_left, hI_V_right, hI_V_len⟩

  let V : CurvilinearRectangle (C * delta) t :=
    { function := U.function, interval := I_V,
      interval_length := by
        have h : I_V.length = Real.sqrt C * L := hI_V_len
        rw [h]
        have h2 : 0 ≤ C := by linarith
        have h3 : Real.sqrt C * L = Real.sqrt (C * delta / t) := by
          rw [show C * delta / t = C * (delta / t) by ring]
          rw [Real.sqrt_mul h2] <;> rfl
        exact h3 }

  -- R.carrier ⊆ V.carrier
  have hR_sub_V : R.carrier ⊆ V.carrier := by
    intro p hp
    have hx : p.1 ∈ R.interval.carrier := hp.1
    have h3 : I_V.left ≤ R.interval.left := by
      have h4 : I_V.left ≤ hL := hI_V_left
      have h5 : hL ≤ R.interval.left := by simp [hL] <;> omega
      linarith
    have h5 : R.interval.right ≤ I_V.right := by
      have h6 : hR ≤ I_V.right := hI_V_right
      have h7 : R.interval.right ≤ hR := by simp [hR] <;> omega
      linarith
    have h_x_in_IV : p.1 ∈ I_V.carrier :=
      ⟨by linarith [h3, hx.1], by linarith [h5, hx.2]⟩
    have h_val1 : |p.2 - R.function p.1| ≤ delta := hp.2
    have h_val2 : |R.function p.1 - U.function p.1| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta :=
      hBound_R p.1 hx
    have h_sum : |p.2 - U.function p.1| ≤ |p.2 - R.function p.1| + |R.function p.1 - U.function p.1| := by
      have h_eq : p.2 - U.function p.1 = (p.2 - R.function p.1) + (R.function p.1 - U.function p.1) := by ring
      rw [h_eq]; exact abs_add_le _ _
    have h_val3 : |p.2 - U.function p.1| ≤ C * delta := by
      have h9 : |p.2 - U.function p.1| ≤ delta + C_comp * Real.rpow (100 : ℝ) 3 * delta := by
        linarith [h_sum, h_val1, h_val2]
      have h_rpow : Real.rpow (100 : ℝ) 3 = (100 : ℝ)^3 := by simp [Real.rpow_natCast]
      rw [h_rpow] at h9
      have h10 : delta + C_comp * (100 : ℝ)^3 * delta = (C_comp * (100 : ℝ)^3 + 1) * delta := by ring
      rw [h10] at h9
      have h11 : (C_comp * (100 : ℝ)^3 + 1) * delta ≤ C * delta := by
        gcongr <;> linarith
      linarith
    exact ⟨h_x_in_IV, h_val3⟩

  -- S.carrier ⊆ V.carrier
  have hS_sub_V : S.carrier ⊆ V.carrier := by
    intro p hp
    have hx : p.1 ∈ S.interval.carrier := hp.1
    have h3 : I_V.left ≤ S.interval.left := by
      have h4 : I_V.left ≤ hL := hI_V_left
      have h5 : hL ≤ S.interval.left := by simp [hL] <;> omega
      linarith
    have h5 : S.interval.right ≤ I_V.right := by
      have h6 : hR ≤ I_V.right := hI_V_right
      have h7 : S.interval.right ≤ hR := by simp [hR] <;> omega
      linarith
    have h_x_in_IV : p.1 ∈ I_V.carrier :=
      ⟨by linarith [h3, hx.1], by linarith [h5, hx.2]⟩
    have h_val1 : |p.2 - S.function p.1| ≤ delta := hp.2
    have h_val2 : |S.function p.1 - U.function p.1| ≤ C_comp * Real.rpow (100 : ℝ) 3 * delta :=
      hBound_S p.1 hx
    have h_sum : |p.2 - U.function p.1| ≤ |p.2 - S.function p.1| + |S.function p.1 - U.function p.1| := by
      have h_eq : p.2 - U.function p.1 = (p.2 - S.function p.1) + (S.function p.1 - U.function p.1) := by ring
      rw [h_eq]; exact abs_add_le _ _
    have h_val3 : |p.2 - U.function p.1| ≤ C * delta := by
      have h9 : |p.2 - U.function p.1| ≤ delta + C_comp * Real.rpow (100 : ℝ) 3 * delta := by
        linarith [h_sum, h_val1, h_val2]
      have h_rpow : Real.rpow (100 : ℝ) 3 = (100 : ℝ)^3 := by simp [Real.rpow_natCast]
      rw [h_rpow] at h9
      have h10 : delta + C_comp * (100 : ℝ)^3 * delta = (C_comp * (100 : ℝ)^3 + 1) * delta := by ring
      rw [h10] at h9
      have h11 : (C_comp * (100 : ℝ)^3 + 1) * delta ≤ C * delta := by
        gcongr <;> linarith
      linarith
    exact ⟨h_x_in_IV, h_val3⟩

  have hComp_RS : R.AreLambdaComparable S family C :=
    ⟨V, hUfam, Set.union_subset hR_sub_V hS_sub_V⟩

  exact hIncomp hComp_RS

end Kakeya.Cinematic
