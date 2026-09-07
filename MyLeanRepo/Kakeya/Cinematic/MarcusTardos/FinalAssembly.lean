import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Final assembly of Marcus-Tardos Theorem 1

Pure algebraic derivation combining the intermediate bounds.
-/

namespace MarcusTardos.FinalAssembly

open Real

/--
Quadratic dichotomy: from `p^2 - B*p - C ≤ 0` with B, C ≥ 0 and p > 0,
prove either `p ≤ 2*B` or `p^2 ≤ 2*C`.
-/
lemma quadratic_dichotomy (p B C : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : p^2 - B*p - C ≤ 0) :
    p ≤ 2*B ∨ p^2 ≤ 2*C := by
  by_cases h' : p ≤ 2*B
  · exact Or.inl h'
  · have h1 : 2*B < p := by linarith
    have h2 : B < p/2 := by linarith
    have h3 : p^2 - B*p > p^2/2 := by nlinarith
    have h4 : p^2 - B*p ≤ C := by linarith
    have h5 : p^2/2 < C := by linarith
    exact Or.inr (by nlinarith)

/--
From the combined bound, derive the dichotomy.
-/
lemma main_dichotomy (C : ℝ) (hC_pos : 0 < C)
    (d m p W V U : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hp : 0 < p)
    (hW : 0 < W) (hV : 0 < V) (hU : 0 ≤ U)
    (h : -m*d^2*U ≤ p*W - p^2/(C*m^2*V)) :
    p ≤ 2*C*m^2*W*V ∨ p^2 ≤ 2*C*m^3*d^2*U*V := by
  let B := C*m^2*W*V
  let D := C*m^3*d^2*U*V
  have hB : 0 ≤ B := by positivity
  have hD : 0 ≤ D := by positivity
  have h1 : 0 < C*m^2*V := by positivity
  have hq : p^2 - B*p - D ≤ 0 := by
    have h2 : -C*m^3*d^2*U*V ≤ C*m^2*p*W*V - p^2 := by
      calc
        -C*m^3*d^2*U*V
          = C*m^2*V * (-m*d^2*U) := by ring
        _ ≤ C*m^2*V * (p*W - p^2/(C*m^2*V)) := by gcongr
        _ = C*m^2*p*W*V - p^2 := by
          field_simp [h1.ne'] <;> ring
    dsimp only [B, D]
    linarith
  have h' := quadratic_dichotomy p B D hp hB hD hq
  rcases h' with (h' | h')
  · have h_goal : p ≤ 2*C*m^2*W*V := by
      have h_eq : p ≤ 2*B := h'
      dsimp only [B] at h_eq
      linarith
    exact Or.inl h_goal
  · have h_goal : p^2 ≤ 2*C*m^3*d^2*U*V := by
      have h_eq : p^2 ≤ 2*D := h'
      dsimp only [D] at h_eq
      linarith
    exact Or.inr h_goal

/-- Case 1 bound: d ≤ 4*√(n*W*V). -/
lemma case1_bound (C : ℝ) (hC_pos : 0 < C)
    (d m n p W V : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hd : 0 < d)
    (hW : 0 < W) (hV : 0 < V)
    (h1 : p ≤ 2*C*m^2*W*V)
    (h2 : d^2*m^2/(2*n) ≤ p) :
    d ≤ 2*Real.sqrt C * Real.sqrt (n*W*V) := by
  have h3 : d^2*m^2/(2*n) ≤ 2*C*m^2*W*V := by linarith
  have h4 : d^2 ≤ 4*C*n*W*V := by
    have h5 : 0 < m^2 := by positivity
    have h6 : 0 < n := hn
    have h7 : d^2*m^2 ≤ 4*C*n*m^2*W*V := by
      calc
        d^2*m^2 = (d^2*m^2/(2*n)) * (2*n) := by
          field_simp [h6.ne'] <;> ring
        _ ≤ (2*C*m^2*W*V) * (2*n) := by gcongr
        _ = 4*C*n*m^2*W*V := by ring
    nlinarith
  have h5 : 0 ≤ n*W*V := by positivity
  have h6 : d ≤ Real.sqrt (4*C*n*W*V) := le_sqrt_of_sq_le h4
  have h7 : Real.sqrt (4*C*n*W*V) = 2*Real.sqrt C * Real.sqrt (n*W*V) := by
    have h8 : 0 ≤ C := by linarith
    have h9 : 0 ≤ n*W*V := by positivity
    have h10 : Real.sqrt (4*C*n*W*V) = Real.sqrt (4*C) * Real.sqrt (n*W*V) := by
      rw [← Real.sqrt_mul (by positivity)] <;> ring_nf
    rw [h10]
    have h11 : Real.sqrt (4*C) = 2*Real.sqrt C := by
      have h12 : 0 ≤ C := h8
      have h13 : Real.sqrt (4*C) = Real.sqrt 4 * Real.sqrt C := by
        rw [← Real.sqrt_mul (by positivity)] <;> ring
      rw [h13]
      have h14 : Real.sqrt 4 = 2 := by
        have h15 : (0 : ℝ) ≤ 2 := by norm_num
        rw [← Real.sqrt_sq h15] <;> norm_num
      rw [h14] <;> ring
    rw [h11] <;> ring
  rw [h7] at h6
  exact h6

/-- Case 2 bound: d ≤ 6*n*√(U*V)/√m. -/
lemma case2_bound (C : ℝ) (hC_pos : 0 < C)
    (d m n p U V : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hd : 0 < d)
    (hU : 0 ≤ U) (hV : 0 < V)
    (h1 : p^2 ≤ 2*C*m^3*d^2*U*V)
    (h2 : d^2*m^2/(2*n) ≤ p) :
    d ≤ Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m := by
  have h3 : 0 ≤ d^2*m^2/(2*n) := by positivity
  have h4 : (d^2*m^2/(2*n))^2 ≤ p^2 := by
    have h5 : 0 ≤ p := by linarith
    nlinarith
  have h5 : (d^2*m^2/(2*n))^2 ≤ 2*C*m^3*d^2*U*V := by linarith
  have h6 : d^2*m^4 ≤ 8*C*n^2*m^3*U*V := by
    have h7 : (d^2*m^2/(2*n))^2 = d^4*m^4/(4*n^2) := by
      field_simp <;> ring
    rw [h7] at h5
    have h8 : 0 < n := hn
    field_simp [h8.ne'] at h5 ⊢ <;> nlinarith
  have h9 : d^2 ≤ 8*C*n^2*U*V/m := by
    have h10 : 0 < m := hm
    calc
      d^2 = (d^2*m^4) / m^4 := by field_simp [h10.ne'] <;> ring
      _ ≤ (8*C*n^2*m^3*U*V) / m^4 := by gcongr
      _ = 8*C*n^2*U*V/m := by field_simp [h10.ne'] <;> ring
  have h10 : d ≤ Real.sqrt (8*C*n^2*U*V/m) := le_sqrt_of_sq_le h9
  have h11 : 0 ≤ U*V := by positivity
  have h12 : 0 < m := hm
  have h13 : 0 < n := hn
  have h14 : 0 ≤ 8*C := by positivity
  have h15 : (Real.sqrt (8*C*n^2*U*V/m))^2 = 8*C*n^2*U*V/m := by
    rw [Real.sq_sqrt] <;> positivity
  have h16 : (Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m)^2 = 8*C*n^2*U*V/m := by
    have h17 : (Real.sqrt (8*C))^2 = 8*C := by rw [Real.sq_sqrt] <;> positivity
    have h18 : (Real.sqrt (U*V))^2 = U*V := by rw [Real.sq_sqrt] <;> positivity
    have h19 : (Real.sqrt m)^2 = m := by rw [Real.sq_sqrt] <;> linarith
    calc
      (Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m)^2
        = (Real.sqrt (8*C))^2 * n^2 * (Real.sqrt (U*V))^2 / (Real.sqrt m)^2 := by ring
      _ = (8*C) * n^2 * (U*V) / m := by rw [h17, h18, h19] <;> ring
      _ = 8*C*n^2*U*V/m := by ring
  have h20 : 0 ≤ Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m := by positivity
  have h21 : Real.sqrt (8*C*n^2*U*V/m) = Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m := by
    have h_pos1 : 0 ≤ Real.sqrt (8*C*n^2*U*V/m) := by positivity
    have h_pos2 : 0 ≤ Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m := by positivity
    have h_eq : (Real.sqrt (8*C*n^2*U*V/m))^2 = (Real.sqrt (8*C) * n * Real.sqrt (U*V) / Real.sqrt m)^2 := by
      rw [h15, h16]
    nlinarith
  rw [h21] at h10
  exact h10

/-- Edge case: d*m ≤ 2*n implies d ≤ 2*n/√m. -/
lemma edge_case_bound (d m n : ℝ) (hm : 1 ≤ m) (hn : 0 < n) (hd : 0 ≤ d)
    (h : d*m ≤ 2*n) : d ≤ 2*n/sqrt m := by
  have h1 : 0 < m := by linarith
  have h2 : d ≤ 2*n/m := by
    calc d = d*m/m := by field_simp [h1.ne'] <;> ring
         _ ≤ (2*n)/m := by gcongr
  have h3 : 1 ≤ sqrt m := by
    have h4 : 1 ≤ m := hm
    have h5 : sqrt 1 ≤ sqrt m := sqrt_le_sqrt h4
    have h6 : sqrt 1 = 1 := by simp
    linarith
  have h7 : 0 < sqrt m := by
    exact sqrt_pos.mpr h1
  have h8 : 1/m ≤ 1/sqrt m := by
    have h9 : 0 ≤ m := by linarith
    have h10 : (sqrt m)^2 = m := sq_sqrt h9
    have h11 : sqrt m ≤ m := by
      have h12 : 1 ≤ sqrt m := h3
      have h13 : 0 ≤ sqrt m := by positivity
      nlinarith [h10]
    have h14 : 0 < sqrt m := h7
    have h15 : 0 < m := h1
    exact one_div_le_one_div_of_le h14 h11
  calc
    d ≤ 2*n/m := h2
    _ = 2*n*(1/m) := by ring
    _ ≤ 2*n*(1/sqrt m) := by gcongr
    _ = 2*n/sqrt m := by ring

end MarcusTardos.FinalAssembly
