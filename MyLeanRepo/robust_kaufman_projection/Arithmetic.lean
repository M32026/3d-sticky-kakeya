module

public import MyLeanRepo.robust_kaufman_projection.Base

@[expose] public section

/-!
# ENNReal and Real arithmetic helpers

Utility lemmas for ENNReal powers, real powers, and covering numbers.
These are used throughout the robust Kaufman projection proof.

## Main results

### ENNReal power lemmas
- `ennreal_ofReal_rpow`: `ofReal (x^s) = (ofReal x)^s` for `x > 0`
- `ennreal_ofReal_div`: `ofReal (x/y) = ofReal x / ofReal y` for `y > 0`
- `ennreal_ofReal_le_iff`: `ofReal a ≤ ofReal b ↔ a ≤ b` when `b ≥ 0`

### Real power lemmas
- `exists_delta_log_le_pow`: `log(1/δ) ≤ δ^(-ε)` for small δ
- `delta_pow_monotone`: if `0 < δ ≤ 1` and `a ≤ b`, then `δ^b ≤ δ^a`
- `real_rpow_add`: `x^(a+b) = x^a * x^b` for `x > 0`
- `real_rpow_neg`: `x^(-a) = (x^a)⁻¹` for `x > 0`

### Covering number lemmas
- `ncover_mono`: monotonicity in set argument
- `ncover_finset_le_card`: covering number of finite set ≤ cardinality
- `ncover_image_lipschitz`: Lipschitz image covering number bound
- `enat_mul_iInf`: multiplication distributes over iInf in ENat
- `ncover_prod_bound`: product covering number bound
-/

noncomputable section

open scoped ENNReal NNReal

namespace RobustKaufmanProjection.Arithmetic

/-! ## ENNReal power lemmas -/

/-- `ENNReal.ofReal (x ^ s) = (ENNReal.ofReal x) ^ s` for `x > 0`. -/
lemma ennreal_ofReal_rpow {x s : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (x ^ s) = (ENNReal.ofReal x) ^ s :=
  (ENNReal.ofReal_rpow_of_pos hx).symm

/-- `ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y` for `y > 0`. -/
lemma ennreal_ofReal_div {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y :=
  ENNReal.ofReal_div_of_pos hy

/-- `ENNReal.ofReal a ≤ ENNReal.ofReal b ↔ a ≤ b` when `b ≥ 0`. -/
lemma ennreal_ofReal_le_iff {a b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b ↔ a ≤ b :=
  ENNReal.ofReal_le_ofReal_iff hb

/-! ## Real power lemmas -/

/-- For any `ε > 0`, there exists `δ₀ > 0` such that for all `0 < δ ≤ δ₀`,
    `Real.log (1 / δ) ≤ δ ^ (-ε)`. -/
lemma exists_delta_log_le_pow (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Real.log (1 / δ) ≤ δ ^ (-ε) := by
  have hε2 : 0 < ε / 2 := by linarith
  have h_main : ∀ x : ℝ, 1 < x → (2 / ε) ≤ x ^ (ε / 2) → Real.log x ≤ x ^ ε := by
    intro x hx hbound
    have h1 : Real.log x ≤ x ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (by linarith) hε2
    have h2 : x ^ (ε / 2) / (ε / 2) = (2 / ε) * x ^ (ε / 2) := by
      field_simp [hε.ne'] <;> ring
    rw [h2] at h1
    have h3 : (2 / ε) * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) := by
      have h4 : 0 < x ^ (ε / 2) := Real.rpow_pos_of_pos (by linarith) (ε / 2)
      nlinarith
    have h5 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
      have h_sum : ε / 2 + ε / 2 = ε := by ring
      rw [← Real.rpow_add (by linarith) (ε / 2) (ε / 2), h_sum]
    rw [h5] at h3
    linarith
  have h_exists : ∃ x0 : ℝ, 1 < x0 ∧ (2 / ε) ≤ x0 ^ (ε / 2) := by
    by_cases hM : (2 / ε) ≤ 1
    · refine ⟨2, by norm_num, ?_⟩
      have h : (1 : ℝ) ≤ (2 : ℝ) ^ (ε / 2) := Real.one_le_rpow (by norm_num) (by linarith)
      linarith
    · have hM' : 1 < (2 / ε) := by linarith
      let x0 := (2 / ε) ^ (2 / ε)
      have hx0_gt_one : 1 < x0 := Real.one_lt_rpow hM' (by positivity)
      have h6 : x0 ^ (ε / 2) = (2 / ε) := by
        have h7 : x0 ^ (ε / 2) = (2 / ε) ^ ((2 / ε) * (ε / 2)) := by
          rw [Real.rpow_mul (by linarith)] <;> rfl
        rw [h7]
        have h8 : (2 / ε) * (ε / 2) = 1 := by field_simp [hε.ne'] <;> ring
        rw [h8]; simp
      exact ⟨x0, hx0_gt_one, by rw [h6] <;> linarith⟩
  rcases h_exists with ⟨x0, hx01, hx02⟩
  refine ⟨1 / x0, by positivity, fun δ hδ hδ₁ => ?_⟩
  have h_x : x0 ≤ 1 / δ := by
    have h7 : δ ≤ 1 / x0 := hδ₁
    calc 1 / δ ≥ 1 / (1 / x0) := by gcongr
         _ = x0 := by field_simp
  have h9 : 1 < 1 / δ := by linarith
  have h10 : (2 / ε) ≤ (1 / δ) ^ (ε / 2) := by
    have h11 : x0 ^ (ε / 2) ≤ (1 / δ) ^ (ε / 2) :=
      Real.rpow_le_rpow (by linarith) h_x (by linarith)
    linarith
  have h13 : Real.log (1 / δ) ≤ (1 / δ) ^ ε := h_main (1 / δ) h9 h10
  have h14 : (1 / δ) ^ ε = δ ^ (-ε) := by
    have h15 : (1 / δ) = δ⁻¹ := by field_simp
    rw [h15]
    rw [Real.inv_rpow (by linarith), Real.rpow_neg (by linarith)]
  rw [h14] at h13
  exact h13

/-- If `0 < δ ≤ 1` and `a ≤ b`, then `δ ^ b ≤ δ ^ a`. -/
lemma delta_pow_monotone {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : a ≤ b) :
    δ ^ b ≤ δ ^ a := by
  have h1 : 0 ≤ b - a := by linarith
  have h2 : δ ^ (b - a) ≤ 1 := by
    have h3 : δ ^ (b - a) ≤ 1 ^ (b - a) := Real.rpow_le_rpow (by linarith) hδ1 h1
    simpa using h3
  have h4 : δ ^ b = δ ^ a * δ ^ (b - a) := by
    have h_sum : a + (b - a) = b := by ring
    rw [← Real.rpow_add hδ a (b - a), h_sum]
  rw [h4]
  have h5 : 0 < δ ^ a := Real.rpow_pos_of_pos hδ a
  nlinarith

/-- For `x > 0`, `x ^ (a + b) = x ^ a * x ^ b`. -/
lemma real_rpow_add {x a b : ℝ} (hx : 0 < x) :
    x ^ (a + b) = x ^ a * x ^ b :=
  Real.rpow_add hx a b

/-- For `x > 0`, `x ^ (-a) = (x ^ a)⁻¹`. -/
lemma real_rpow_neg {x a : ℝ} (hx : 0 < x) :
    x ^ (-a) = (x ^ a)⁻¹ :=
  Real.rpow_neg (by linarith) a

/-! ## Covering number lemmas -/

/-- External covering number is monotone in the set argument. -/
lemma ncover_mono {X : Type*} [PseudoMetricSpace X] {δ : ℝ} {A B : Set X} (h : A ⊆ B) :
    Ncover δ A ≤ Ncover δ B := by
  have h' : Metric.externalCoveringNumber δ.toNNReal A ≤ Metric.externalCoveringNumber δ.toNNReal B :=
    Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h
  simpa [Ncover] using h'

/-- The external covering number of a finite set is at most its cardinality. -/
lemma ncover_finset_le_card {X : Type*} [PseudoMetricSpace X] {δ : ℝ} (hδ : 0 ≤ δ)
    (S : Finset X) :
    Ncover δ (S : Set X) ≤ (S.card : ENNReal) := by
  let δ' : NNReal := δ.toNNReal
  have h1 : Metric.externalCoveringNumber δ' (S : Set X) ≤ (S : Set X).encard :=
    Metric.externalCoveringNumber_le_encard_self (S : Set X)
  have h2 : (S : Set X).encard = (S.card : ENat) := by simp
  rw [h2] at h1
  have h3 : (↑(Metric.externalCoveringNumber δ' (S : Set X)) : ENNReal) ≤ (↑(S.card : ENat) : ENNReal) := by
    exact_mod_cast h1
  simpa [Ncover] using h3

/-- If `f` is `LipschitzWith K`, then `Ncover (K * δ) (f '' A) ≤ Ncover δ A`. -/
lemma ncover_image_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : NNReal} {f : X → Y} (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ)
    {A : Set X} :
    Ncover (K * δ) (f '' A) ≤ Ncover δ A := by
  let δ' : NNReal := δ.toNNReal
  let Kδ' : NNReal := K * δ'
  have hKδ_eq : (↑K * δ).toNNReal = Kδ' := by
    apply NNReal.coe_injective
    have h_nonneg : 0 ≤ ↑K * δ := by positivity
    have h1 : ((↑K * δ).toNNReal : ℝ) = ↑K * δ := Real.coe_toNNReal (↑K * δ) h_nonneg
    have h2 : (Kδ' : ℝ) = ↑K * δ := by
      have h21 : (Kδ' : ℝ) = ↑K * ↑δ' := by simp [Kδ', NNReal.coe_mul]
      have h22 : (↑δ' : ℝ) = δ := Real.coe_toNNReal δ hδ
      rw [h21, h22]
    rw [h1, h2]
  have h_main : Metric.externalCoveringNumber Kδ' (f '' A) ≤ Metric.externalCoveringNumber δ' A := by
    apply le_iInf₂
    intro C hC
    have h_img : Metric.IsCover Kδ' (f '' A) (f '' C) :=
      Metric.IsCover.image_lipschitz hC hf
    have h1 : Metric.externalCoveringNumber Kδ' (f '' A) ≤ (f '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_img
    have h2 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
    exact le_trans h1 h2
  have h_goal : Ncover (↑K * δ) (f '' A) ≤ Ncover δ A := by
    simp only [Ncover]
    have h3 : (↑K * δ).toNNReal = Kδ' := hKδ_eq
    rw [h3]
    exact_mod_cast h_main
  exact h_goal

/-- Helper: `a * iInf f = iInf (a * f i)` for `a ≠ 0` in `ENat`. -/
lemma enat_mul_iInf {ι : Sort*} {f : ι → ENat} {a : ENat} (ha : a ≠ 0) :
    a * iInf f = iInf (fun i : ι => a * f i) := by
  have h1 : (iInf f) * a = iInf (fun i : ι => f i * a) := ENat.iInf_mul_of_ne ha
  have h2 : a * iInf f = (iInf f) * a := by rw [mul_comm]
  have h3 : iInf (fun i : ι => f i * a) = iInf (fun i : ι => a * f i) := by
    congr; funext i; rw [mul_comm]
  rw [h2, h1, h3]

/-- Product covering number bound with max metric on product. -/
lemma ncover_prod_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {A : Set X} {B : Set Y} {δ : ℝ} (hδ : 0 ≤ δ) :
    Ncover δ (A ×ˢ B) ≤ Ncover δ A * Ncover δ B := by
  let δ' : NNReal := δ.toNNReal
  set eA : ENat := Metric.externalCoveringNumber δ' A with heA
  set eB : ENat := Metric.externalCoveringNumber δ' B with heB
  set eAB : ENat := Metric.externalCoveringNumber δ' (A ×ˢ B) with heAB

  have hδ' : δ' = δ.toNNReal := by rfl
  have hN_A : Ncover δ A = (eA : ENNReal) := by
    simp [Ncover, heA, hδ']
  have hN_B : Ncover δ B = (eB : ENNReal) := by
    simp [Ncover, heB, hδ']
  have hN_AB : Ncover δ (A ×ˢ B) = (eAB : ENNReal) := by
    simp [Ncover, heAB, hδ']
  rw [hN_AB, hN_A, hN_B]

  have h_forall : ∀ (CA : Set X), Metric.IsCover δ' A CA →
      ∀ (CB : Set Y), Metric.IsCover δ' B CB →
        eAB ≤ CA.encard * CB.encard := by
    intro CA hCA CB hCB
    have h_prod_cover : Metric.IsCover δ' (A ×ˢ B) (CA ×ˢ CB) := by
      intro p hp
      rcases p with ⟨x, y⟩
      rcases hp with ⟨hx, hy⟩
      rcases hCA hx with ⟨cA, hcA, hdistA⟩
      rcases hCB hy with ⟨cB, hcB, hdistB⟩
      have hA' : edist x cA ≤ ↑δ' := by simpa using hdistA
      have hB' : edist y cB ≤ ↑δ' := by simpa using hdistB
      refine ⟨(cA, cB), ⟨hcA, hcB⟩, ?_⟩
      have h : edist (x, y) (cA, cB) ≤ ↑δ' := by
        rw [Prod.edist_eq]
        exact max_le hA' hB'
      exact h
    have h1 : eAB ≤ (CA ×ˢ CB).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_prod_cover
    have h2 : (CA ×ˢ CB).encard = CA.encard * CB.encard := Set.encard_prod
    rw [h2] at h1
    exact h1

  -- Handle edge cases
  by_cases hA_zero : eA = 0
  · have hA_empty : A = ∅ := Metric.externalCoveringNumber_eq_zero.mp hA_zero
    have h_goal : (eAB : ENNReal) ≤ (eA : ENNReal) * (eB : ENNReal) := by
      rw [hA_empty] at heAB
      simp [heAB, hA_zero]
    exact h_goal
  by_cases hB_zero : eB = 0
  · have hB_empty : B = ∅ := Metric.externalCoveringNumber_eq_zero.mp hB_zero
    have h_goal : (eAB : ENNReal) ≤ (eA : ENNReal) * (eB : ENNReal) := by
      rw [hB_empty] at heAB
      simp [heAB, hB_zero]
    exact h_goal
  by_cases hA_top : eA = ⊤
  · have h_goal : (eAB : ENNReal) ≤ (eA : ENNReal) * (eB : ENNReal) := by
      have h_ne_zero : (eB : ENNReal) ≠ 0 := by exact_mod_cast hB_zero
      rw [hA_top]
      simp [h_ne_zero] <;> exact le_top
    exact h_goal
  by_cases hB_top : eB = ⊤
  · have h_goal : (eAB : ENNReal) ≤ (eA : ENNReal) * (eB : ENNReal) := by
      have h_ne_zero : (eA : ENNReal) ≠ 0 := by exact_mod_cast hA_zero
      rw [hB_top]
      simp [h_ne_zero] <;> exact le_top
    exact h_goal

  -- Main case: all nonzero and nontop
  have h_step1 : ∀ (CA : Set X), Metric.IsCover δ' A CA →
      eAB ≤ CA.encard * eB := by
    intro CA hCA
    by_cases hCA_zero : CA.encard = 0
    · have hCA_empty : CA = ∅ := by simpa [Set.encard_eq_zero] using hCA_zero
      have hA_empty : A = ∅ := by
        by_contra hA
        have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
        have h_contra := Metric.IsCover.nonempty hCA hA_nonempty
        rw [hCA_empty] at h_contra
        simpa using h_contra
      rw [hA_empty] at heAB
      simp [heAB, hCA_zero]
    have h_outer : CA.encard * (⨅ (CB : Set Y), ⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) =
        ⨅ (CB : Set Y), CA.encard * (⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) :=
      @enat_mul_iInf (Set Y) (fun CB => ⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) CA.encard hCA_zero
    have h_inner : ∀ (CB : Set Y), CA.encard * (⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) =
        ⨅ (hCB : Metric.IsCover δ' B CB), CA.encard * CB.encard := by
      intro CB
      exact @enat_mul_iInf (Metric.IsCover δ' B CB) (fun _ => CB.encard) CA.encard hCA_zero
    have h_mul : CA.encard * eB =
        ⨅ (CB : Set Y), ⨅ (hCB : Metric.IsCover δ' B CB), CA.encard * CB.encard := by
      calc
        CA.encard * eB
          = CA.encard * (⨅ (CB : Set Y), ⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) := by
            rw [heB, Metric.externalCoveringNumber]
        _ = ⨅ (CB : Set Y), CA.encard * (⨅ (hCB : Metric.IsCover δ' B CB), CB.encard) := h_outer
        _ = ⨅ (CB : Set Y), ⨅ (hCB : Metric.IsCover δ' B CB), CA.encard * CB.encard := by
          congr; funext CB; exact h_inner CB
    rw [h_mul]
    apply le_iInf₂
    intro CB hCB
    exact h_forall CA hCA CB hCB

  have h_outer2 : eB * (⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) =
      ⨅ (CA : Set X), eB * (⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) :=
    @enat_mul_iInf (Set X) (fun CA => ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) eB hB_zero
  have h_inner2 : ∀ (CA : Set X), eB * (⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) =
      ⨅ (hCA : Metric.IsCover δ' A CA), eB * CA.encard := by
    intro CA
    exact @enat_mul_iInf (Metric.IsCover δ' A CA) (fun _ => CA.encard) eB hB_zero
  have h_mul_final : eA * eB =
      ⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard * eB := by
    have h_eA_def : eA = ⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard := by
      rw [heA, Metric.externalCoveringNumber]
    calc
      eA * eB
        = eB * eA := by rw [mul_comm]
      _ = eB * (⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) := by
        rw [h_eA_def]
      _ = ⨅ (CA : Set X), eB * (⨅ (hCA : Metric.IsCover δ' A CA), CA.encard) := h_outer2
      _ = ⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), eB * CA.encard := by
        congr; funext CA; exact h_inner2 CA
      _ = ⨅ (CA : Set X), ⨅ (hCA : Metric.IsCover δ' A CA), CA.encard * eB := by
        congr with CA; congr with hCA; rw [mul_comm]
  have h_final : eAB ≤ eA * eB := by
    rw [h_mul_final]
    apply le_iInf₂
    intro CA hCA
    exact h_step1 CA hCA
  have h_coe : ((eAB : ENNReal)) ≤ (eA : ENNReal) * (eB : ENNReal) := by
    exact_mod_cast h_final
  exact h_coe

/-! ## Polynomial loss accounting -/

/-- For any constant `C > 0` and `ε > 0`, there exists `δ₀ > 0` with `δ₀ ≤ 1`
    such that for all `0 < δ ≤ δ₀`, `C ≤ δ ^ (-ε)`. -/
lemma delta_pow_absorb_const (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-ε) := by
  let δ₀ : ℝ := min 1 (C ^ (-1 / ε))
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := min_le_left _ _
  have hδ₀_le : δ₀ ≤ C ^ (-1 / ε) := min_le_right _ _
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, fun δ hδ hδ_le => ?_⟩
  have h1 : δ ≤ C ^ (-1 / ε) := le_trans hδ_le hδ₀_le
  have h2 : 0 < C ^ (-1 / ε) := by positivity
  have h3 : δ ^ ε ≤ (C ^ (-1 / ε)) ^ ε := Real.rpow_le_rpow (by linarith) h1 (by linarith)
  have h4 : (C ^ (-1 / ε)) ^ ε = C⁻¹ := by
    rw [← Real.rpow_mul (by linarith)]
    have h5 : (-1 / ε) * ε = -1 := by field_simp [hε.ne'] <;> ring
    rw [h5]
    have h6 : C ^ (-1 : ℝ) = C⁻¹ := by
      rw [Real.rpow_neg (by linarith)]
      <;> simp
    exact h6
  have h6 : δ ^ ε ≤ C⁻¹ := by
    rw [h4] at h3
    exact h3
  have h7 : 0 < δ ^ ε := by positivity
  have h8 : C ≤ (δ ^ ε)⁻¹ := by
    have h9 : 0 < C⁻¹ := by positivity
    have h10 : (δ ^ ε)⁻¹ ≥ C := by
      calc (δ ^ ε)⁻¹ ≥ (C⁻¹)⁻¹ := by gcongr
           _ = C := by simp
    exact h10
  have h11 : (δ ^ ε)⁻¹ = δ ^ (-ε) := by
    rw [Real.rpow_neg (by linarith)] <;> ring
  rw [h11] at h8
  exact h8

/-- For any `C > 0` and `ε > 0`, there exists `δ₀ > 0` such that
    for all `0 < δ ≤ δ₀`, `C * Real.log (1 / δ) ≤ δ ^ (-ε)`. -/
lemma delta_pow_absorb_const_log (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      C * Real.log (1 / δ) ≤ δ ^ (-ε) := by
  have hε2 : 0 < ε / 2 := by linarith
  rcases delta_pow_absorb_const C (ε / 2) hC hε2 with ⟨δ₁, hδ₁_pos, hδ₁_le_one, h1⟩
  rcases exists_delta_log_le_pow (ε / 2) hε2 with ⟨δ₂, hδ₂_pos, h2⟩
  let δ₀ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    calc δ₀ ≤ δ₁ := min_le_left _ _
         _ ≤ 1 := hδ₁_le_one
  refine ⟨δ₀, hδ₀_pos, fun δ hδ hδ_le => ?_⟩
  have hδ_le₁ : δ ≤ δ₁ := by
    exact le_trans hδ_le (min_le_left _ _)
  have hδ_le₂ : δ ≤ δ₂ := by
    exact le_trans hδ_le (min_le_right _ _)
  have hδ_le_one : δ ≤ 1 := by linarith
  have h3 : C ≤ δ ^ (-(ε / 2)) := h1 δ hδ hδ_le₁
  have h4 : Real.log (1 / δ) ≤ δ ^ (-(ε / 2)) := h2 δ hδ hδ_le₂
  have h5 : 0 ≤ Real.log (1 / δ) := by
    have h6 : 1 ≤ 1 / δ := by
      apply one_le_one_div <;> linarith
    exact Real.log_nonneg h6
  have h7 : C * Real.log (1 / δ) ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
    calc
      C * Real.log (1 / δ)
        ≤ δ ^ (-(ε / 2)) * Real.log (1 / δ) := by
          exact mul_le_mul_of_nonneg_right h3 h5
      _ ≤ δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h9 : δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) = δ ^ (-ε) := by
    rw [← Real.rpow_add hδ]
    have h10 : -(ε / 2) + (-(ε / 2)) = -ε := by ring
    rw [h10]
  rw [h9] at h7
  exact h7

/-- Product of δ-powers: `δ^a * δ^b = δ^(a+b)` for `δ > 0`. -/
lemma delta_pow_product {δ a b : ℝ} (hδ : 0 < δ) :
    δ ^ a * δ ^ b = δ ^ (a + b) :=
  (Real.rpow_add hδ a b).symm

/-- ENNReal product of δ-powers:
    `ofReal(δ^a) * ofReal(δ^b) = ofReal(δ^(a+b))` for `δ > 0`. -/
lemma ennreal_delta_pow_product {δ a b : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b) = ENNReal.ofReal (δ ^ (a + b)) := by
  have h1 : 0 ≤ δ ^ a := by positivity
  rw [← ENNReal.ofReal_mul h1, delta_pow_product hδ]

/-- For `0 < δ ≤ 1`, if `a ≤ b`, then `δ^b ≤ δ^a`.
    (Larger exponents give smaller values for bases in (0,1].) -/
lemma delta_pow_decreasing {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : a ≤ b) :
    δ ^ b ≤ δ ^ a :=
  delta_pow_monotone hδ hδ1 h

/-- ENNReal version: for `0 < δ ≤ 1`, if `a ≤ b`, then
    `ofReal(δ^b) ≤ ofReal(δ^a)`. -/
lemma ennreal_delta_pow_decreasing {δ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : a ≤ b) :
    ENNReal.ofReal (δ ^ b) ≤ ENNReal.ofReal (δ ^ a) := by
  have h1 : δ ^ b ≤ δ ^ a := delta_pow_decreasing hδ hδ1 h
  have h2 : 0 ≤ δ ^ a := by positivity
  exact ENNReal.ofReal_le_ofReal h1

/-- Absorb a log factor into a δ-power: if `a, ε > 0` and `0 < δ ≤ 1`, then
    `δ^(-a) * log(1/δ) ≤ δ^(-(a + ε))` given `log(1/δ) ≤ δ^(-ε)`. -/
lemma delta_pow_absorb_log {δ a ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (hε : 0 < ε)
    (h : Real.log (1 / δ) ≤ δ ^ (-ε)) :
    δ ^ (-a) * Real.log (1 / δ) ≤ δ ^ (-(a + ε)) := by
  have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
    have h3 : 1 ≤ 1 / δ := by
      have h4 : δ ≤ 1 := hδ1
      have h5 : 0 < δ := hδ
      calc 1 / δ ≥ 1 / 1 := by gcongr
           _ = 1 := by norm_num
    exact Real.log_nonneg h3
  have h_mul : δ ^ (-a) * Real.log (1 / δ) ≤ δ ^ (-a) * δ ^ (-ε) := by
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h_eq : δ ^ (-a) * δ ^ (-ε) = δ ^ (-(a + ε)) := by
    rw [← Real.rpow_add hδ]
    have h4 : -a + (-ε) = -(a + ε) := by ring
    rw [h4]
  rw [h_eq] at h_mul
  exact h_mul

/-- For small δ, any constant `C` can be absorbed: `C * δ^(-a) ≤ δ^(-(a + ε))`. -/
lemma delta_pow_absorb_const_mul {δ a ε C : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hε : 0 < ε)
    (hC : 0 ≤ C) (h : C ≤ δ ^ (-ε)) :
    C * δ ^ (-a) ≤ δ ^ (-(a + ε)) := by
  have h1 : C * δ ^ (-a) ≤ δ ^ (-ε) * δ ^ (-a) := by
    gcongr <;> positivity
  have h2 : δ ^ (-ε) * δ ^ (-a) = δ ^ (-(a + ε)) := by
    rw [← Real.rpow_add hδ]
    have h3 : -ε + (-a) = -(a + ε) := by ring
    rw [h3]
  rw [h2] at h1
  exact h1

end RobustKaufmanProjection.Arithmetic
