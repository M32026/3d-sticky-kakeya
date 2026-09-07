import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.LogAbsorption
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Dyadic assembly helpers for WZ1 Lemma 44

Finite dyadic scale family construction, logarithmic loss absorption,
finite-union cardinality bounds, complement retention, and the
good-pair tube-count reduction used in the quarter-thin-tubes
final assembly.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open BigOperators

/-- Helper: `2^(Real.logb 2 x) = x` for `x > 0`. -/
private lemma rpow_logb_two {x : ℝ} (hx : 0 < x) :
    (2 : ℝ)^(Real.logb 2 x) = x := by
  have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 * Real.logb 2 x = Real.log x := by
    simp only [Real.logb]
    field_simp [hln2_pos.ne']
  have h : (2 : ℝ)^(Real.logb 2 x) =
      Real.exp (Real.log 2 * Real.logb 2 x) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
  rw [h, h2, Real.exp_log hx]

/--
Dyadic rounding: for any `r ≥ δ > 0`, there exists `k : ℕ` such that
`r ≤ δ * 2^k` and `δ * 2^k < 2 * r`.
-/
lemma dyadic_rounding {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) :
    ∃ k : ℕ, r ≤ δ * (2 : ℝ)^k ∧ δ * (2 : ℝ)^k < 2 * r := by
  have hr_pos : 0 < r := hδ.trans_le hr
  set x : ℝ := r / δ with hx_def
  have hx_one : 1 ≤ x := by
    dsimp only [x]
    rw [one_le_div hδ] <;> linarith
  have hx_pos : 0 < x := by positivity
  let y : ℝ := Real.logb 2 x
  let k : ℕ := Nat.ceil y
  have hy_nonneg : 0 ≤ y := by
    dsimp only [y]
    apply Real.logb_nonneg
    <;> norm_num <;> linarith
  have h1 : y ≤ (k : ℝ) := Nat.le_ceil _
  have h2 : (k : ℝ) < y + 1 := Nat.ceil_lt_add_one hy_nonneg
  have h_rpow_logb : (2 : ℝ)^y = x := rpow_logb_two hx_pos
  have h3 : x ≤ (2 : ℝ)^(k : ℝ) := by
    have h : (2 : ℝ)^y ≤ (2 : ℝ)^(k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rw [h_rpow_logb] at h
    exact h
  have h4 : (2 : ℝ)^(k : ℝ) < 2 * x := by
    have h : (2 : ℝ)^(k : ℝ) < (2 : ℝ)^(y + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
    have h5 : (2 : ℝ)^(y + 1) = 2 * (2 : ℝ)^y := by
      rw [Real.rpow_add (by norm_num)] <;> ring
    rw [h5, h_rpow_logb] at h
    exact h
  have h_cast : (2 : ℝ)^k = (2 : ℝ)^(k : ℝ) := by norm_cast
  refine ⟨k, ?_, ?_⟩
  · have h6 : r = δ * x := by
      dsimp only [x] <;> field_simp [hδ.ne'] <;> ring
    rw [h6, h_cast]
    exact mul_le_mul_of_nonneg_left h3 hδ.le
  · rw [h_cast]
    have h7 : δ * (2 : ℝ)^(k : ℝ) < δ * (2 * x) :=
      mul_lt_mul_of_pos_left h4 hδ
    have h8 : δ * (2 * x) = 2 * r := by
      dsimp only [x]
      field_simp [hδ.ne'] <;> ring
    rw [h8] at h7
    exact h7

/--
Finite dyadic scale family.

Given `0 < δ < T`, construct `N := Nat.ceil (Real.logb 2 (T / δ))`
and `scales := {δ * 2^k | k < N}`.
-/
def dyadic_scale_family (δ T : ℝ) : Finset ℝ :=
  let N := Nat.ceil (Real.logb 2 (T / δ))
  Finset.image (fun k : ℕ => δ * (2 : ℝ)^k) (Finset.range N)

namespace dyadic_scale_family

lemma card {δ T : ℝ} (hδ : 0 < δ) (hTδ : δ < T) :
    (dyadic_scale_family δ T).card = Nat.ceil (Real.logb 2 (T / δ)) := by
  dsimp only [dyadic_scale_family]
  let N := Nat.ceil (Real.logb 2 (T / δ))
  have h_inj : Function.Injective (fun k : ℕ => δ * (2 : ℝ)^k) := by
    intro k1 k2 h
    have h9 : (2 : ℝ)^k1 = (2 : ℝ)^k2 := by
      apply (mul_right_inj' hδ.ne').mp
      exact h
    have h9' : (2 : ℕ)^k1 = (2 : ℕ)^k2 := by exact_mod_cast h9
    have h10 : k1 = k2 := Nat.pow_right_injective (by norm_num) h9'
    exact h10
  rw [Finset.card_image_of_injective _ h_inj, Finset.card_range]

lemma all_lt_T {δ T : ℝ} (hδ : 0 < δ) (hTδ : δ < T)
    {R : ℝ} (hR : R ∈ dyadic_scale_family δ T) : R < T := by
  dsimp only [dyadic_scale_family] at hR
  rcases Finset.mem_image.mp hR with ⟨k, hk, rfl⟩
  let N := Nat.ceil (Real.logb 2 (T / δ))
  have hkN : k < N := Finset.mem_range.mp hk
  have hT_pos : 0 < T := by linarith [hδ, hTδ]
  have hx_pos : 0 < T / δ := div_pos hT_pos hδ
  have h_k_lt_x : (k : ℝ) < Real.logb 2 (T / δ) := by
    by_contra h
    have h' : (k : ℝ) ≥ Real.logb 2 (T / δ) := by linarith
    have h_ceil_le_k : N ≤ k := Nat.ceil_le.mpr h'
    exact not_le.mpr hkN h_ceil_le_k
  have h_rpow_lt : (2 : ℝ)^(k : ℝ) < (2 : ℝ)^(Real.logb 2 (T / δ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_k_lt_x
  have h_rpow_logb : (2 : ℝ)^(Real.logb 2 (T / δ)) = T / δ :=
    rpow_logb_two hx_pos
  rw [h_rpow_logb] at h_rpow_lt
  have h_cast : (2 : ℝ)^k = (2 : ℝ)^(k : ℝ) := by norm_cast
  rw [h_cast]
  have h : δ * (2 : ℝ)^(k : ℝ) < δ * (T / δ) :=
    mul_lt_mul_of_pos_left h_rpow_lt hδ
  have h9 : δ * (T / δ) = T := by
    field_simp [hδ.ne'] <;> ring
  rw [h9] at h
  exact h

lemma next_ge_T {δ T : ℝ} (hδ : 0 < δ) (hTδ : δ < T) :
    T ≤ δ * (2 : ℝ)^(Nat.ceil (Real.logb 2 (T / δ))) := by
  let N := Nat.ceil (Real.logb 2 (T / δ))
  have hT_pos : 0 < T := by linarith [hδ, hTδ]
  have h1 : Real.logb 2 (T / δ) ≤ (N : ℝ) := Nat.le_ceil _
  have hx_pos : 0 < T / δ := div_pos hT_pos hδ
  have h_rpow_logb : (2 : ℝ)^(Real.logb 2 (T / δ)) = T / δ :=
    rpow_logb_two hx_pos
  have h : (2 : ℝ)^(Real.logb 2 (T / δ)) ≤ (2 : ℝ)^(N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [h_rpow_logb] at h
  have h_cast : (2 : ℝ)^N = (2 : ℝ)^(N : ℝ) := by norm_cast
  rw [h_cast]
  have h2 : T / δ ≤ (2 : ℝ)^(N : ℝ) := h
  have h3 : δ * (T / δ) ≤ δ * (2 : ℝ)^(N : ℝ) :=
    mul_le_mul_of_nonneg_left h2 hδ.le
  have h4 : δ * (T / δ) = T := by
    field_simp [hδ.ne'] <;> ring
  rw [h4] at h3
  exact h3

lemma N_bound {δ T : ℝ} (hδ : 0 < δ) (hTδ : δ < T) :
    (Nat.ceil (Real.logb 2 (T / δ)) : ℝ) ≤ Real.logb 2 (T / δ) + 1 := by
  have h_one_le : 1 ≤ T / δ := by
    rw [one_le_div hδ] <;> linarith
  have hlog_nonneg : 0 ≤ Real.logb 2 (T / δ) :=
    Real.logb_nonneg (by norm_num) h_one_le
  have h : (Nat.ceil (Real.logb 2 (T / δ)) : ℝ) < Real.logb 2 (T / δ) + 1 :=
    Nat.ceil_lt_add_one hlog_nonneg
  linarith

lemma pos {δ T : ℝ} (hδ : 0 < δ) (hTδ : δ < T)
    {R : ℝ} (hR : R ∈ dyadic_scale_family δ T) : 0 < R := by
  rcases Finset.mem_image.mp hR with ⟨k, _, rfl⟩
  positivity

end dyadic_scale_family

/--
Logarithmic absorption for the quarter-thin-tubes assembly.

For any fixed `C > 0` and `α > 0`, there exists `δ₀ > 0` such that
for all `0 < δ ≤ δ₀`:
`C * (Real.logb 2 (1 / δ) + 1) * δ^(2 * α) ≤ δ^α`.
-/
lemma quarter_thin_tubes_log_absorption (C α : ℝ) (hC : 0 < C) (halpha : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        C * (Real.logb 2 (1 / δ) + 1) * Real.rpow δ (2 * α) ≤ Real.rpow δ α := by
  have h_main := Kakeya.Cinematic.localAssembly_logb_absorption_general
    C 1 α hC (by norm_num) halpha
  rcases h_main with ⟨δ₀, hδ₀_pos, hδ₀_one, h⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_one, ?_⟩
  intro δ hδ hδ₀
  have h1 : C * (Real.logb 2 (1 / δ) + 1) ≤ Real.rpow δ (-α) := h δ hδ hδ₀
  have h4 : Real.rpow δ (-α) * Real.rpow δ (2 * α) = Real.rpow δ α := by
    have h_add : Real.rpow δ (-α) * Real.rpow δ (2 * α) =
        Real.rpow δ ((-α) + (2 * α)) := (Real.rpow_add hδ _ _).symm
    rw [h_add]
    have h_sum : (-α) + (2 * α) = α := by ring
    rw [h_sum]
  have h_rpow_nonneg : 0 ≤ Real.rpow δ (2 * α) := Real.rpow_nonneg (by linarith) _
  calc
    C * (Real.logb 2 (1 / δ) + 1) * Real.rpow δ (2 * α)
      ≤ Real.rpow δ (-α) * Real.rpow δ (2 * α) :=
        mul_le_mul_of_nonneg_right h1 h_rpow_nonneg
    _ = Real.rpow δ α := h4

/--
Finite bad-pair union bound.

If each `bad i ⊆ G₁ ×ˢ G₂` has cardinality at most
`C0 * |G₁| * |G₂|`, then the union over `scales` has
cardinality at most `|scales| * C0 * |G₁| * |G₂|`.
-/
lemma finite_bad_union_bound
    {ι : Type*} [DecidableEq ι]
    {scales : Finset ι}
    {bad : ι → Finset (Point2 × Point2)}
    {G₁ G₂ : DiscreteSet 2}
    {C0 : ℝ}
    (hbad_card : ∀ i ∈ scales,
      (bad i).card ≤ C0 * (G₁.card : ℝ) * (G₂.card : ℝ)) :
    ((scales.biUnion bad).card : ℝ) ≤
      (scales.card : ℝ) * C0 * (G₁.card : ℝ) * (G₂.card : ℝ) := by
  have h1 : ((scales.biUnion bad).card : ℝ) ≤ ∑ i ∈ scales, ((bad i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h2 : ∑ i ∈ scales, ((bad i).card : ℝ) ≤
      ∑ i ∈ scales, (C0 * (G₁.card : ℝ) * (G₂.card : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hbad_card i hi
  have h3 : ∑ i ∈ scales, (C0 * (G₁.card : ℝ) * (G₂.card : ℝ)) =
      (scales.card : ℝ) * C0 * (G₁.card : ℝ) * (G₂.card : ℝ) := by
    rw [Finset.sum_const]
    <;> ring
  linarith

/--
Complement retention.

If `bad ⊆ G₁ ×ˢ G₂` and `bad.card ≤ c * |G₁| * |G₂|` with `0 ≤ c ≤ 1`,
then the complement `E := (G₁ ×ˢ G₂) \\ bad` satisfies
`(1 - ENNReal.ofReal c) * |G₁| * |G₂| ≤ |E|` in `ENNReal`.
-/
lemma complement_retention
    {G₁ G₂ : DiscreteSet 2}
    {bad : Finset (Point2 × Point2)}
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hbad_sub : bad ⊆ G₁ ×ˢ G₂)
    (hbad_card : (bad.card : ℝ) ≤ c * (G₁.card : ℝ) * (G₂.card : ℝ)) :
    (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) ≤
      (((G₁ ×ˢ G₂) \ bad).card : ENNReal) := by
  have h1 : ((G₁ ×ˢ G₂).card : ℝ) = (G₁.card : ℝ) * (G₂.card : ℝ) := by
    simp [Finset.card_product] <;> ring
  have h2 : (((G₁ ×ˢ G₂) \ bad).card : ℝ) =
      ((G₁ ×ˢ G₂).card : ℝ) - (bad.card : ℝ) := by
    have h21 : ((G₁ ×ˢ G₂) \ bad).card = (G₁ ×ˢ G₂).card - bad.card :=
      Finset.card_sdiff_of_subset hbad_sub
    rw [h21, Nat.cast_sub (Finset.card_le_card hbad_sub)] <;> rfl
  have hbad_card2 : (bad.card : ℝ) ≤ c * ((G₁ ×ˢ G₂).card : ℝ) := by
    calc (bad.card : ℝ)
      ≤ c * (G₁.card : ℝ) * (G₂.card : ℝ) := hbad_card
    _ = c * ((G₁ ×ˢ G₂).card : ℝ) := by rw [h1] <;> ring
  have h3 : (((G₁ ×ˢ G₂) \ bad).card : ℝ) ≥
      (1 - c) * ((G₁ ×ˢ G₂).card : ℝ) := by
    rw [h2]
    linarith [hbad_card2]
  have h4 : 0 ≤ (1 - c) * ((G₁ ×ˢ G₂).card : ℝ) := by
    have h5 : 0 ≤ 1 - c := by linarith
    positivity
  have h6 : (1 - ENNReal.ofReal c) = ENNReal.ofReal (1 - c) := by
    have h61 : ENNReal.ofReal (1 - c) = ENNReal.ofReal (1 : ℝ) - ENNReal.ofReal c :=
      ENNReal.ofReal_sub (1 : ℝ) hc0
    have h62 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
    rw [h62] at h61
    exact h61.symm
  rw [h6]
  have h7 : ENNReal.ofReal (1 - c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) =
      ENNReal.ofReal ((1 - c) * (G₁.card : ℝ) * (G₂.card : ℝ)) := by
    have h_pos1 : 0 ≤ (1 - c) := by linarith
    have h_pos2 : 0 ≤ (G₁.card : ℝ) := by positivity
    have h_pos3 : 0 ≤ (G₂.card : ℝ) := by positivity
    simp [ENNReal.ofReal_mul, h_pos1, h_pos2, h_pos3, mul_assoc]
    <;> ring
  rw [h7]
  have h8 : (1 - c) * (G₁.card : ℝ) * (G₂.card : ℝ) =
      (1 - c) * ((G₁ ×ˢ G₂).card : ℝ) := by
    rw [h1] <;> ring
  rw [h8]
  have h9 : (((G₁ ×ˢ G₂) \ bad).card : ENNReal) =
      ENNReal.ofReal (((G₁ ×ˢ G₂) \ bad).card : ℝ) := by
    simp
  rw [h9]
  exact ENNReal.ofReal_le_ofReal h3

/--
Good-pair tube count bound.

If every pair in `E` is not bad at scale `R` with constant `K_int`, then for
any line `ℓ` through `b₁` and any `r ≤ R`, the number of `b₂ ∈ G₂` such that
`b₂` lies in the `r`-thickening of `ℓ` and `(b₁, b₂) ∈ E` is at most
`K_int * R^(1/4) * |G₂|`.
-/
lemma good_pair_tube_bound
    {G₁ G₂ : DiscreteSet 2}
    {E : Finset (Point2 × Point2)}
    {K_int R : ℝ}
    (h_not_bad : ∀ (b₁ : Point2), b₁ ∈ G₁ → ∀ (b₂ : Point2), b₂ ∈ G₂ →
      (b₁, b₂) ∈ E → ¬ WZ1BadAtScale G₁ G₂ R K_int b₁ b₂)
    {b₁ : Point2} (hb₁ : b₁ ∈ G₁)
    (ℓ : AffineSubspace ℝ Point2)
    (hb₁_line : b₁ ∈ (ℓ : Set Point2))
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    {r : ℝ} (hr : r ≤ R) :
    ((G₂.filter fun b₂ =>
      b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E).card : ENNReal) ≤
    ENNReal.ofReal (K_int * Real.rpow R (1 / 4 : ℝ)) * G₂.enncard := by
  let S := G₂.filter fun b₂ =>
    b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E
  let T_filt := G₂.filter fun point => point ∈ Metric.thickening R (ℓ : Set Point2)
  have hS_sub_T : S ⊆ T_filt := by
    intro b₂ hb₂
    have h1 : b₂ ∈ G₂ := (Finset.mem_filter.mp hb₂).1
    have h2 : b₂ ∈ Metric.thickening r (ℓ : Set Point2) :=
      (Finset.mem_filter.mp hb₂).2.1
    have h3 : b₂ ∈ Metric.thickening R (ℓ : Set Point2) :=
      Metric.thickening_mono (by linarith) _ h2
    exact Finset.mem_filter.mpr ⟨h1, h3⟩
  by_cases hS_empty : S = ∅
  · simp only [S, hS_empty]
    <;> simp
  · have hS_nonempty : S.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty]
    rcases hS_nonempty with ⟨b₂, hb₂⟩
    have hb₂_G₂ : b₂ ∈ G₂ := (Finset.mem_filter.mp hb₂).1
    have hb₂_thick : b₂ ∈ Metric.thickening r (ℓ : Set Point2) :=
      (Finset.mem_filter.mp hb₂).2.1
    have hb₂_E : (b₁, b₂) ∈ E := (Finset.mem_filter.mp hb₂).2.2
    have hb₂_Rthick : b₂ ∈ Metric.thickening R (ℓ : Set Point2) :=
      Metric.thickening_mono (by linarith) _ hb₂_thick
    have h_not_heavy : ¬ WZ1BadAtScale G₁ G₂ R K_int b₁ b₂ :=
      h_not_bad b₁ hb₁ b₂ hb₂_G₂ hb₂_E
    have h_heavy_bound : (T_filt.card : ENNReal) ≤
        ENNReal.ofReal (K_int * Real.rpow R (1 / 4 : ℝ)) * G₂.enncard := by
      by_contra h
      have h' : (T_filt.card : ENNReal) >
          ENNReal.ofReal (K_int * Real.rpow R (1 / 4 : ℝ)) * G₂.enncard :=
        not_le.mp h
      have h_bad : WZ1BadAtScale G₁ G₂ R K_int b₁ b₂ := by
        refine ⟨ℓ, hb₁_line, hfin, hb₂_Rthick, ?_⟩
        simpa [T_filt] using h'
      exact h_not_heavy h_bad
    have hS_card : (S.card : ENNReal) ≤ (T_filt.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hS_sub_T
    exact hS_card.trans h_heavy_bound

end Kakeya.Assouad
