module

/-
  Dyadic square correspondence under homothety rescaling.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.LinearToRegular
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- Under rescaling by `1/Δ^a`, the `Δ^(a+k)`-square with indices
    `(i*n^k + a', j*n^k + b')` maps exactly to the `Δ^k`-square `(a', b')`. -/
lemma rescaled_square_image
    {Δ : ℝ} {a k : ℕ} {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    (i j a' b' : ℤ) :
    let L : ℝ := 1 / (Δ ^ a)
    let v : EuclideanPlane :=
      WithLp.toLp (2 : ENNReal) (fun k : Fin 2 =>
        if k = 0 then (i : ℝ) * (Δ ^ a) else (j : ℝ) * (Δ ^ a))
    let τ : EuclideanPlane → EuclideanPlane := fun x => L • (x - v)
    let c : ℤ := i * (n ^ k) + a'
    let d : ℤ := j * (n ^ k) + b'
    τ '' (dyadicSquare (Δ ^ (a + k)) c d) = dyadicSquare (Δ ^ k) a' b' := by
  let L : ℝ := 1 / (Δ ^ a)
  let v : EuclideanPlane :=
    WithLp.toLp (2 : ENNReal) (fun k : Fin 2 =>
      if k = 0 then (i : ℝ) * (Δ ^ a) else (j : ℝ) * (Δ ^ a))
  let τ : EuclideanPlane → EuclideanPlane := fun x => L • (x - v)
  let c : ℤ := i * (n ^ k) + a'
  let d : ℤ := j * (n ^ k) + b'
  let R := dyadicSquare (Δ ^ (a + k)) c d
  let R' := dyadicSquare (Δ ^ k) a' b'
  have hΔ_pos : 0 < Δ := by
    have h : (n : ℝ) * Δ = 1 := by linarith
    have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  have hΔa_pos : 0 < Δ ^ a := by positivity
  have h_div_k : (n : ℝ) ^ k * Δ ^ k = 1 := by
    have h : (n : ℝ) ^ k * Δ ^ k = ((n : ℝ) * Δ) ^ k := by rw [←mul_pow] <;> ring
    rw [h, ←h1] <;> norm_num
  have h_cast_ik : ((i * n ^ k : ℤ) : ℝ) = (i : ℝ) * (n : ℝ) ^ k := by simp <;> ring
  have h_cast_jk : ((j * n ^ k : ℤ) : ℝ) = (j : ℝ) * (n : ℝ) ^ k := by simp <;> ring
  have h_ik : ((i * n ^ k : ℤ) : ℝ) * Δ ^ (a + k) = (i : ℝ) * (Δ ^ a) := by
    calc ((i * n ^ k : ℤ) : ℝ) * Δ ^ (a + k)
      = ((i : ℝ) * (n : ℝ) ^ k) * Δ ^ (a + k) := by rw [h_cast_ik]
    _ = (i : ℝ) * ((n : ℝ) ^ k * Δ ^ (a + k)) := by ring
    _ = (i : ℝ) * ((n : ℝ) ^ k * (Δ ^ a * Δ ^ k)) := by rw [show Δ ^ (a + k) = Δ ^ a * Δ ^ k by rw [pow_add]]
    _ = (i : ℝ) * (Δ ^ a * ((n : ℝ) ^ k * Δ ^ k)) := by ring
    _ = (i : ℝ) * (Δ ^ a * 1) := by rw [h_div_k] <;> ring
    _ = (i : ℝ) * (Δ ^ a) := by ring
  have h_jk : ((j * n ^ k : ℤ) : ℝ) * Δ ^ (a + k) = (j : ℝ) * (Δ ^ a) := by
    calc ((j * n ^ k : ℤ) : ℝ) * Δ ^ (a + k)
      = ((j : ℝ) * (n : ℝ) ^ k) * Δ ^ (a + k) := by rw [h_cast_jk]
    _ = (j : ℝ) * ((n : ℝ) ^ k * Δ ^ (a + k)) := by ring
    _ = (j : ℝ) * ((n : ℝ) ^ k * (Δ ^ a * Δ ^ k)) := by rw [show Δ ^ (a + k) = Δ ^ a * Δ ^ k by rw [pow_add]]
    _ = (j : ℝ) * (Δ ^ a * ((n : ℝ) ^ k * Δ ^ k)) := by ring
    _ = (j : ℝ) * (Δ ^ a * 1) := by rw [h_div_k] <;> ring
    _ = (j : ℝ) * (Δ ^ a) := by ring
  have h_c : (c : ℝ) * Δ ^ (a + k) = (a' : ℝ) * Δ ^ (a + k) + (i : ℝ) * (Δ ^ a) := by
    have h_def : (c : ℝ) = (a' : ℝ) + ((i * n ^ k : ℤ) : ℝ) := by simp [c] <;> ring
    rw [h_def, add_mul, h_ik] <;> ring
  have h_c1 : (c + 1 : ℝ) * Δ ^ (a + k) = (a' + 1 : ℝ) * Δ ^ (a + k) + (i : ℝ) * (Δ ^ a) := by
    have h_def : (c + 1 : ℝ) = (a' + 1 : ℝ) + ((i * n ^ k : ℤ) : ℝ) := by simp [c] <;> ring
    rw [h_def, add_mul, h_ik] <;> ring
  have h_d : (d : ℝ) * Δ ^ (a + k) = (b' : ℝ) * Δ ^ (a + k) + (j : ℝ) * (Δ ^ a) := by
    have h_def : (d : ℝ) = (b' : ℝ) + ((j * n ^ k : ℤ) : ℝ) := by simp [d] <;> ring
    rw [h_def, add_mul, h_jk] <;> ring
  have h_d1 : (d + 1 : ℝ) * Δ ^ (a + k) = (b' + 1 : ℝ) * Δ ^ (a + k) + (j : ℝ) * (Δ ^ a) := by
    have h_def : (d + 1 : ℝ) = (b' + 1 : ℝ) + ((j * n ^ k : ℤ) : ℝ) := by simp [d] <;> ring
    rw [h_def, add_mul, h_jk] <;> ring
  have h_div_eq : ∀ (x : ℝ), x * Δ ^ k = (x * Δ ^ (a + k)) / (Δ ^ a) := by
    intro x
    have h2 : Δ ^ (a + k) = Δ ^ a * Δ ^ k := by rw [pow_add]
    have h : (x * Δ ^ (a + k)) / (Δ ^ a) = x * Δ ^ k := by
      rw [h2]
      have h4 : (x * (Δ ^ a * Δ ^ k)) / (Δ ^ a) = x * Δ ^ k := by
        field_simp [hΔa_pos.ne'] <;> ring
      exact h4
    exact h.symm
  ext z
  simp only [Set.mem_image, dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · rintro ⟨w, h_w, rfl⟩
    have h_w01 : (c : ℝ) * Δ ^ (a + k) ≤ w 0 := h_w.1.1
    have h_w02 : w 0 < (c + 1 : ℝ) * Δ ^ (a + k) := h_w.1.2
    have h_w11 : (d : ℝ) * Δ ^ (a + k) ≤ w 1 := h_w.2.1
    have h_w12 : w 1 < (d + 1 : ℝ) * Δ ^ (a + k) := h_w.2.2
    have h_tw0 : (τ w) 0 = (w 0 - (i : ℝ) * (Δ ^ a)) / (Δ ^ a) := by
      have h : (τ w) 0 = L * ((w - v) 0) := by simp [τ, Pi.smul_apply] <;> ring
      rw [h] <;> simp [v, L] <;> ring
    have h_tw1 : (τ w) 1 = (w 1 - (j : ℝ) * (Δ ^ a)) / (Δ ^ a) := by
      have h : (τ w) 1 = L * ((w - v) 1) := by simp [τ, Pi.smul_apply] <;> ring
      rw [h] <;> simp [v, L] <;> ring
    rw [h_tw0, h_tw1]
    have h01 : (a' : ℝ) * Δ ^ (a + k) ≤ w 0 - (i : ℝ) * (Δ ^ a) := by
      have h : (c : ℝ) * Δ ^ (a + k) = (a' : ℝ) * Δ ^ (a + k) + (i : ℝ) * (Δ ^ a) := h_c
      linarith
    have h02 : w 0 - (i : ℝ) * (Δ ^ a) < (a' + 1 : ℝ) * Δ ^ (a + k) := by
      have h : (c + 1 : ℝ) * Δ ^ (a + k) = (a' + 1 : ℝ) * Δ ^ (a + k) + (i : ℝ) * (Δ ^ a) := h_c1
      linarith
    have h11 : (b' : ℝ) * Δ ^ (a + k) ≤ w 1 - (j : ℝ) * (Δ ^ a) := by
      have h : (d : ℝ) * Δ ^ (a + k) = (b' : ℝ) * Δ ^ (a + k) + (j : ℝ) * (Δ ^ a) := h_d
      linarith
    have h12 : w 1 - (j : ℝ) * (Δ ^ a) < (b' + 1 : ℝ) * Δ ^ (a + k) := by
      have h : (d + 1 : ℝ) * Δ ^ (a + k) = (b' + 1 : ℝ) * Δ ^ (a + k) + (j : ℝ) * (Δ ^ a) := h_d1
      linarith
    have h_goal01 : (a' : ℝ) * Δ ^ k ≤ (w 0 - (i : ℝ) * (Δ ^ a)) / (Δ ^ a) := by
      rw [h_div_eq (a' : ℝ)]
      exact div_le_div_of_nonneg_right h01 (by positivity)
    have h_goal02 : (w 0 - (i : ℝ) * (Δ ^ a)) / (Δ ^ a) < (a' + 1 : ℝ) * Δ ^ k := by
      rw [h_div_eq (a' + 1 : ℝ)]
      exact div_lt_div_of_pos_right h02 hΔa_pos
    have h_goal11 : (b' : ℝ) * Δ ^ k ≤ (w 1 - (j : ℝ) * (Δ ^ a)) / (Δ ^ a) := by
      rw [h_div_eq (b' : ℝ)]
      exact div_le_div_of_nonneg_right h11 (by positivity)
    have h_goal12 : (w 1 - (j : ℝ) * (Δ ^ a)) / (Δ ^ a) < (b' + 1 : ℝ) * Δ ^ k := by
      rw [h_div_eq (b' + 1 : ℝ)]
      exact div_lt_div_of_pos_right h12 hΔa_pos
    exact ⟨⟨h_goal01, h_goal02⟩, ⟨h_goal11, h_goal12⟩⟩
  · rintro h_z
    let w : EuclideanPlane :=
      WithLp.toLp (2 : ENNReal) (fun k : Fin 2 =>
        if k = 0 then (Δ ^ a) * z 0 + (i : ℝ) * (Δ ^ a)
        else (Δ ^ a) * z 1 + (j : ℝ) * (Δ ^ a))
    have h_w0_def : w 0 = (Δ ^ a) * z 0 + (i : ℝ) * (Δ ^ a) := by simp [w] <;> rfl
    have h_w1_def : w 1 = (Δ ^ a) * z 1 + (j : ℝ) * (Δ ^ a) := by simp [w] <;> rfl
    have h_tw0 : (τ w) 0 = z 0 := by
      simp [τ, w, v, Pi.smul_apply, L]
      <;> field_simp [hΔa_pos.ne'] <;> ring
    have h_tw1 : (τ w) 1 = z 1 := by
      simp [τ, w, v, Pi.smul_apply, L]
      <;> field_simp [hΔa_pos.ne'] <;> ring
    have h_z01 : (a' : ℝ) * Δ ^ k ≤ z 0 := h_z.1.1
    have h_z02 : z 0 < (a' + 1 : ℝ) * Δ ^ k := h_z.1.2
    have h_z11 : (b' : ℝ) * Δ ^ k ≤ z 1 := h_z.2.1
    have h_z12 : z 1 < (b' + 1 : ℝ) * Δ ^ k := h_z.2.2
    have h_w01 : (c : ℝ) * Δ ^ (a + k) ≤ w 0 := by
      rw [h_c, h_w0_def]
      have h4 : (a' : ℝ) * Δ ^ (a + k) = (Δ ^ a) * ((a' : ℝ) * Δ ^ k) := by
        rw [pow_add] <;> ring
      rw [h4]
      nlinarith
    have h_w02 : w 0 < (c + 1 : ℝ) * Δ ^ (a + k) := by
      rw [h_c1, h_w0_def]
      have h4 : (a' + 1 : ℝ) * Δ ^ (a + k) = (Δ ^ a) * ((a' + 1 : ℝ) * Δ ^ k) := by
        rw [pow_add] <;> ring
      rw [h4]
      nlinarith
    have h_w11 : (d : ℝ) * Δ ^ (a + k) ≤ w 1 := by
      rw [h_d, h_w1_def]
      have h4 : (b' : ℝ) * Δ ^ (a + k) = (Δ ^ a) * ((b' : ℝ) * Δ ^ k) := by
        rw [pow_add] <;> ring
      rw [h4]
      nlinarith
    have h_w12 : w 1 < (d + 1 : ℝ) * Δ ^ (a + k) := by
      rw [h_d1, h_w1_def]
      have h4 : (b' + 1 : ℝ) * Δ ^ (a + k) = (Δ ^ a) * ((b' + 1 : ℝ) * Δ ^ k) := by
        rw [pow_add] <;> ring
      rw [h4]
      nlinarith
    have h_wR : w ∈ R := by
      simp only [R, dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
      exact ⟨⟨h_w01, h_w02⟩, ⟨h_w11, h_w12⟩⟩
    have h_tau_eq : τ w = z := by
      ext k
      fin_cases k <;> simp [h_tw0, h_tw1] <;> tauto
    exact ⟨w, h_wR, h_tau_eq⟩

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
