import MyLeanRepo.Kakeya.CV.Statements

/-!
# Polynomial visibility theorem

Final degree-selection assembly after the finite bad-set avoidance theorem.
-/

namespace Kakeya.CV

private lemma choose_two_formula (k : ℕ) :
    2 * Nat.choose (k + 2) 2 = (k + 1) * (k + 2) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega,
        Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      nlinarith

private lemma choose_three_formula (k : ℕ) :
    6 * Nat.choose (k + 3) 3 = (k + 1) * (k + 2) * (k + 3) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by omega,
        Nat.choose_succ_succ]
      have h2 := choose_two_formula (k + 1)
      nlinarith

private lemma root_cube (x : ℝ) (hx : 0 ≤ x) :
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast]
  convert Real.rpow_inv_natCast_pow hx
    (show (3 : ℕ) ≠ 0 by norm_num) using 1 <;> norm_num

private lemma degree_choice (C S : ℝ) (hC : 0 < C) (hS : 0 ≤ S) :
    let root := Real.rpow (6 * C * S) (1 / 3 : ℝ)
    let k := ⌊root⌋₊
    (k : ℝ) ≤ root ∧ C * S < (Nat.choose (k + 3) 3 : ℝ) := by
  dsimp only
  let root := Real.rpow (6 * C * S) (1 / 3 : ℝ)
  let k := ⌊root⌋₊
  have hbase : 0 ≤ 6 * C * S := by positivity
  have hroot_nonneg : 0 ≤ root := Real.rpow_nonneg hbase _
  have hk_le : (k : ℝ) ≤ root := Nat.floor_le hroot_nonneg
  have hroot_lt : root < (k : ℝ) + 1 := Nat.lt_floor_add_one root
  have hcube : root ^ 3 = 6 * C * S := root_cube _ hbase
  have hpow_lt : root ^ 3 < ((k : ℝ) + 1) ^ 3 :=
    pow_lt_pow_left₀ hroot_lt hroot_nonneg (by norm_num)
  have hprod : ((k : ℝ) + 1) ^ 3 ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    nlinarith [mul_nonneg (by linarith : 0 ≤ (k : ℝ) + 1)
      (by nlinarith : 0 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3))]
  have hchoose_nat := choose_three_formula k
  have hchoose : 6 * (Nat.choose (k + 3) 3 : ℝ) =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
    exact_mod_cast hchoose_nat
  have hchain : 6 * C * S < 6 * (Nat.choose (k + 3) 3 : ℝ) := by
    calc
      6 * C * S = root ^ 3 := hcube.symm
      _ < ((k : ℝ) + 1) ^ 3 := hpow_lt
      _ ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := hprod
      _ = 6 * (Nat.choose (k + 3) 3 : ℝ) := hchoose.symm
  exact ⟨hk_le, by nlinarith [hchain]⟩

theorem polynomial_visibility.{u}
    (hParameter : PolynomialParameterSpaceStatement)
    (hAvoidance : PolynomialBadSetAvoidanceConclusion.{u}) :
    PolynomialVisibilityStatement.{u} := by
  rcases hAvoidance with
    ⟨Ccount, Cvis, hCcount, hCvis, hAvoidance⟩
  let Cdeg : ℝ := Real.rpow (6 * Ccount) (1 / 3 : ℝ)
  have hCdeg : 0 < Cdeg :=
    Real.rpow_pos_of_pos (mul_pos (by norm_num) hCcount) _
  refine ⟨Cdeg, Cvis, hCdeg, hCvis, ?_⟩
  intro Cube _ center M
  let S : ℝ := ∑ q, (M q : ℝ) ^ 3
  have hS : 0 ≤ S := by positivity
  let root : ℝ := Real.rpow (6 * Ccount * S) (1 / 3 : ℝ)
  let k : ℕ := ⌊root⌋₊
  rcases degree_choice Ccount S hCcount hS with
    ⟨hk_root, hdimension⟩
  rcases hParameter k with ⟨P, hPdim⟩
  have hPdim_pos : 0 < P.dim := by
    rw [hPdim]
    exact Nat.choose_pos (by omega)
  have hdimension' :
      Ccount * ∑ q, (M q : ℝ) ^ 3 < (P.dim : ℝ) := by
    simpa [S, k, root, hPdim] using hdimension
  rcases hAvoidance Cube k P center M hPdim_pos hdimension' with
    ⟨ε, x, hε, hx, hvis⟩
  have hroot_eq :
      root = Cdeg * Real.rpow S (1 / 3 : ℝ) := by
    dsimp [root, Cdeg]
    rw [show 6 * Ccount * S = (6 * Ccount) * S by ring]
    exact Real.mul_rpow (by positivity) hS
  refine ⟨k, P, ε, x, hε, hx, ?_, fun q => (hvis q).le⟩
  exact hk_root.trans_eq hroot_eq

end Kakeya.CV
