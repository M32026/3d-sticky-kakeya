module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-
# Common-Scale Comparability

Derives mutual comparability `A ≤ δ^{-q_KA} · B` from two-sided bounds
relative to a **common scale** `X` (e.g. `X = sqrt(N(Pbar))`):

  C_lower · δ^{e_lower} · X ≤ A ≤ C_upper · δ^{e_upper} · X
  C_lower · δ^{e_lower} · X ≤ B ≤ C_upper · δ^{e_upper} · X

The common `X` cancels. Constant factors `C_upper / C_lower` are absorbed
into an additional exponent `e_absorb` via `C_upper ≤ C_lower · δ^{-e_absorb}`.

Result: comparability exponent `e_upper - e_lower - e_absorb`.

## Whiteprint node
`common_scale_comparability`
-/

namespace ProductLikeIncidence.ProductReduction

open ENNReal

/-- **Common-scale comparability** (ENNReal).

Given both A and B satisfy
`C_lower · δ^{e_lower} · X ≤ A ≤ C_upper · δ^{e_upper} · X`
for the same `X`, and constants are absorbable via
`C_upper ≤ C_lower · δ^{-e_absorb}`, then
`A ≤ δ^{e_upper - e_lower - e_absorb} · B` and vice versa. -/
lemma common_scale_comparability
    {δ : ℝ} (hδ_pos : 0 < δ)
    {e_upper e_lower e_absorb : ℝ}
    {X : ENNReal} (hX_pos : 0 < X) (hX_ne_top : X ≠ ⊤)
    {A B : ENNReal}
    {C_upper C_lower : ENNReal}
    (hC_lower_pos : 0 < C_lower) (hC_lower_ne_top : C_lower ≠ ⊤)
    (h_absorb : C_upper ≤ C_lower * ENNReal.ofReal (δ ^ (-e_absorb)))
    (hA_upper : A ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    (hA_lower : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ A)
    (hB_upper : B ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    (hB_lower : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ B) :
    A ≤ ENNReal.ofReal (δ ^ (e_upper - e_lower - e_absorb)) * B ∧
    B ≤ ENNReal.ofReal (δ ^ (e_upper - e_lower - e_absorb)) * A := by
  let X' := C_lower * X
  have hX'_pos : 0 < X' := by
    have h : 0 < C_lower * X := by positivity
    exact h
  have hX'_ne_top : X' ≠ ⊤ := ENNReal.mul_ne_top hC_lower_ne_top hX_ne_top
  let e_upper' := e_upper - e_absorb

  have h_exp1 : δ ^ (-e_absorb) * δ ^ e_upper = δ ^ e_upper' := by
    rw [← Real.rpow_add hδ_pos] <;> simp [e_upper'] <;> ring_nf
  have h_ofReal_mul1 : ENNReal.ofReal (δ ^ (-e_absorb)) * ENNReal.ofReal (δ ^ e_upper) =
      ENNReal.ofReal (δ ^ e_upper') := by
    have h_pos1 : 0 ≤ δ ^ (-e_absorb) := by positivity
    have h_pos2 : 0 ≤ δ ^ e_upper := by positivity
    have h : ENNReal.ofReal (δ ^ (-e_absorb) * δ ^ e_upper) =
        ENNReal.ofReal (δ ^ (-e_absorb)) * ENNReal.ofReal (δ ^ e_upper) := by
      exact ofReal_mul h_pos1
    rw [← h, h_exp1]
  have h_exp2 : δ ^ (e_upper' - e_lower) * δ ^ e_lower = δ ^ e_upper' := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h_ofReal_mul2 : ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * ENNReal.ofReal (δ ^ e_lower) =
      ENNReal.ofReal (δ ^ e_upper') := by
    have h_pos1 : 0 ≤ δ ^ (e_upper' - e_lower) := by positivity
    have h_pos2 : 0 ≤ δ ^ e_lower := by positivity
    have h : ENNReal.ofReal (δ ^ (e_upper' - e_lower) * δ ^ e_lower) =
        ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * ENNReal.ofReal (δ ^ e_lower) := by exact ofReal_mul h_pos1
    rw [← h, h_exp2]

  -- Upper bounds reshaped: A ≤ δ^{e_upper'} * X'
  have hA_upper' : A ≤ ENNReal.ofReal (δ ^ e_upper') * X' := by
    have h1 : C_upper * ENNReal.ofReal (δ ^ e_upper) * X ≤
        (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X := by
      gcongr
    have h2 : (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X =
        C_lower * (ENNReal.ofReal (δ ^ (-e_absorb)) * ENNReal.ofReal (δ ^ e_upper)) * X := by
      simp [mul_assoc]
    have h3 : C_lower * (ENNReal.ofReal (δ ^ (-e_absorb)) * ENNReal.ofReal (δ ^ e_upper)) * X =
        C_lower * ENNReal.ofReal (δ ^ e_upper') * X := by
      rw [h_ofReal_mul1]
    have h4 : C_lower * ENNReal.ofReal (δ ^ e_upper') * X =
        ENNReal.ofReal (δ ^ e_upper') * X' := by
      simp [X', mul_assoc, mul_comm, mul_left_comm]
    calc A
      ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X := hA_upper
    _ ≤ (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X := h1
    _ = C_lower * ENNReal.ofReal (δ ^ e_upper') * X := by rw [h2, h3]
    _ = ENNReal.ofReal (δ ^ e_upper') * X' := h4

  have hB_upper' : B ≤ ENNReal.ofReal (δ ^ e_upper') * X' := by
    have h1 : C_upper * ENNReal.ofReal (δ ^ e_upper) * X ≤
        (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X := by
      gcongr
    have h2 : (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X =
        C_lower * ENNReal.ofReal (δ ^ e_upper') * X := by
      simp [mul_assoc, h_ofReal_mul1]
    have h3 : C_lower * ENNReal.ofReal (δ ^ e_upper') * X =
        ENNReal.ofReal (δ ^ e_upper') * X' := by
      simp [X', mul_assoc, mul_comm, mul_left_comm]
    calc B
      ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X := hB_upper
    _ ≤ (C_lower * ENNReal.ofReal (δ ^ (-e_absorb))) * ENNReal.ofReal (δ ^ e_upper) * X := h1
    _ = C_lower * ENNReal.ofReal (δ ^ e_upper') * X := h2
    _ = ENNReal.ofReal (δ ^ e_upper') * X' := h3

  -- Lower bounds reshaped: δ^{e_lower} * X' ≤ A
  have hA_lower' : ENNReal.ofReal (δ ^ e_lower) * X' ≤ A := by
    have h_eq : C_lower * ENNReal.ofReal (δ ^ e_lower) * X =
        ENNReal.ofReal (δ ^ e_lower) * X' := by
      simp [X', mul_assoc, mul_comm, mul_left_comm]
    have h : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ A := hA_lower
    rw [h_eq] at h
    exact h

  have hB_lower' : ENNReal.ofReal (δ ^ e_lower) * X' ≤ B := by
    have h_eq : C_lower * ENNReal.ofReal (δ ^ e_lower) * X =
        ENNReal.ofReal (δ ^ e_lower) * X' := by
      simp [X', mul_assoc, mul_comm, mul_left_comm]
    have h : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ B := hB_lower
    rw [h_eq] at h
    exact h

  -- Reassociation for comparability step
  have h_reassoc : ENNReal.ofReal (δ ^ e_upper') * X' =
      ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * (ENNReal.ofReal (δ ^ e_lower) * X') := by
    have h : ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * (ENNReal.ofReal (δ ^ e_lower) * X') =
        (ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * ENNReal.ofReal (δ ^ e_lower)) * X' := by
      simp [mul_assoc]
    rw [h, h_ofReal_mul2]

  have hA : A ≤ ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * B := by
    calc A
      ≤ ENNReal.ofReal (δ ^ e_upper') * X' := hA_upper'
    _ = ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * (ENNReal.ofReal (δ ^ e_lower) * X') := h_reassoc
    _ ≤ ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * B := by gcongr
  have hB : B ≤ ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * A := by
    calc B
      ≤ ENNReal.ofReal (δ ^ e_upper') * X' := hB_upper'
    _ = ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * (ENNReal.ofReal (δ ^ e_lower) * X') := h_reassoc
    _ ≤ ENNReal.ofReal (δ ^ (e_upper' - e_lower)) * A := by gcongr

  have h_exp_final : e_upper' - e_lower = e_upper - e_lower - e_absorb := by
    simp [e_upper'] <;> ring
  rw [h_exp_final] at hA hB
  exact ⟨hA, hB⟩

/-- **Convenience: real-valued constants**. -/
lemma common_scale_comparability_real_consts
    {δ : ℝ} (hδ_pos : 0 < δ)
    {e_upper e_lower e_absorb : ℝ}
    {X : ENNReal} (hX_pos : 0 < X) (hX_ne_top : X ≠ ⊤)
    {A B : ENNReal}
    {C_upper C_lower : ℝ} (hC_upper_nonneg : 0 ≤ C_upper) (hC_lower_pos : 0 < C_lower)
    (h_absorb : C_upper ≤ C_lower * δ ^ (-e_absorb))
    (hA_upper : A ≤ ENNReal.ofReal C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    (hA_lower : ENNReal.ofReal C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ A)
    (hB_upper : B ≤ ENNReal.ofReal C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    (hB_lower : ENNReal.ofReal C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ B) :
    A ≤ ENNReal.ofReal (δ ^ (e_upper - e_lower - e_absorb)) * B ∧
    B ≤ ENNReal.ofReal (δ ^ (e_upper - e_lower - e_absorb)) * A := by
  have hC_lower_pos' : 0 < ENNReal.ofReal C_lower := by
    exact ENNReal.ofReal_pos.mpr hC_lower_pos
  have hC_lower_ne_top' : ENNReal.ofReal C_lower ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_absorb' : ENNReal.ofReal C_upper ≤
      ENNReal.ofReal C_lower * ENNReal.ofReal (δ ^ (-e_absorb)) := by
    have h2 : ENNReal.ofReal C_upper ≤ ENNReal.ofReal (C_lower * δ ^ (-e_absorb)) := by
      gcongr
    have h3 : ENNReal.ofReal (C_lower * δ ^ (-e_absorb)) =
        ENNReal.ofReal C_lower * ENNReal.ofReal (δ ^ (-e_absorb)) := by
      have h_pos1 : 0 ≤ C_lower := by linarith
      have h_pos2 : 0 ≤ δ ^ (-e_absorb) := by positivity
      have h : ENNReal.ofReal (C_lower * δ ^ (-e_absorb)) =
          ENNReal.ofReal C_lower * ENNReal.ofReal (δ ^ (-e_absorb)) := by exact ofReal_mul h_pos1
      exact h
    rw [h3] at h2
    exact h2
  exact common_scale_comparability hδ_pos
    hX_pos hX_ne_top
    (C_upper := ENNReal.ofReal C_upper) (C_lower := ENNReal.ofReal C_lower)
    hC_lower_pos' hC_lower_ne_top'
    h_absorb' hA_upper hA_lower hB_upper hB_lower

end ProductLikeIncidence.ProductReduction
