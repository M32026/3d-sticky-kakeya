module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceAssignedNormalizationW97

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_source_pass_numerics_w104 {beta gammaZero eCap : Real}
    (hbeta : 0 < beta) (hgap : beta < gammaZero) (hgamma : gammaZero <= 1)
    (hCap : 0 < eCap) :
    ∃ (p : Params) (xi : Fin (p.N + 1) -> Real) (xiMin : Real) (M : Nat),
      SourcePassNumericsW95 p beta gammaZero xi xiMin M ∧ p.ε <= eCap := by
  let eBound := min eCap (min (1 / 4 : Real) ((gammaZero - beta) / 2000))
  have heBound : 0 < eBound := lt_min hCap (lt_min (by norm_num) (by linarith))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt heBound
  let k := n + 1
  let N := k * k
  let eps : Real := 1 / k
  have hk : (0 : Real) < k := by dsimp [k]; positivity
  have heps : 0 < eps := one_div_pos.mpr hk
  have hepsBound : eps < eBound := by simpa only [eps, k, Nat.cast_add, Nat.cast_one] using hn
  have hepsCap : eps <= eCap := hepsBound.le.trans (min_le_left _ _)
  have heps4 : eps < 1 / 4 := hepsBound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hepsGap : eps <= (gammaZero - beta) / 2000 :=
    hepsBound.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hk4 : (4 : Real) < k := by
    have hh := (div_lt_iff₀ hk).mp heps4
    nlinarith
  have hN : 5 <= N := by
    have hkN : 5 <= k := by exact_mod_cast hk4
    dsimp only [N]
    nlinarith
  have hepsEq : eps = (N : Real) ^ (-(1 / 2 : Real)) := by
    dsimp only [eps, N]
    rw [Nat.cast_mul, ← sq, ← Real.rpow_natCast, ← Real.rpow_mul hk.le]
    norm_num [Real.rpow_neg_one]
  let q : Real := min (eps / 100) (min (1 / 2) (eps ^ 2 * beta / 1600000))
  have hq : 0 < q := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hqE : q <= eps / 100 := min_le_left _ _
  have hqHalf : q <= 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hqBeta : q <= eps ^ 2 * beta / 1600000 := (min_le_right _ _).trans (min_le_right _ _)
  have hq1 : q <= 1 := hqHalf.trans (by norm_num)
  let zeta : Nat -> Real := fun m => (eps / 10) * q ^ (N - m)
  have hzeta : ∀ m, 0 < zeta m := by intro m; dsimp only [zeta]; positivity
  have hmono : ∀ a b, a <= b -> b <= N -> zeta a <= zeta b := by
    intro a b hab hb
    dsimp only [zeta]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one hq.le hq1 (Nat.sub_le_sub_left hab N)
  have hzetaTop : zeta N = eps / 10 := by simp only [zeta, Nat.sub_self, pow_zero, mul_one]
  have hzetaUpper : ∀ m, m <= N -> zeta m <= eps / 10 := by
    intro m hm
    rw [← hzetaTop]
    exact hmono m N hm le_rfl
  have hzetaStep : ∀ m, m < N -> zeta m = q * zeta (m + 1) := by
    intro m hm
    dsimp only [zeta]
    rw [show N - m = (N - (m + 1)) + 1 by omega, pow_succ]
    ring
  let xi : Fin (N + 1) -> Real := fun m => 200 * zeta m.val
  let xiMin := 200 * zeta 0
  have hxiMin : 0 < xiMin := by dsimp only [xiMin]; positivity
  let gridBound := min (eps * zeta 0 / 160000)
    (min (eps * xiMin / 200) (eps ^ 2 * zeta 0 / 192))
  have hgridBound : 0 < gridBound := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hgridBound
  let M := j + 1
  have hM : 1 <= M := by dsimp only [M]; omega
  have hGrid : (1 : Real) / M <= gridBound := by
    simpa only [M, Nat.cast_add, Nat.cast_one] using hj.le
  have hGridZeta : (1 : Real) / M <= eps * zeta 0 / 160000 := hGrid.trans (min_le_left _ _)
  let p : Params :=
    { ηStar := eCap
      δ₀ := 1
      N := N
      ε := eps
      κ := q
      η := zeta
      ε' := zeta 0 / 16
      ηGamma := fun _ => zeta 0
      c := min (gammaZero / 2) (zeta 0 / 4) }
  refine ⟨p, xi, xiMin, M, ?_, hepsCap⟩
  refine
    { beta_pos := hbeta
      gammaZero_gt := hgap
      gammaZero_le := hgamma
      N_large := hN
      epsilon_eq := hepsEq
      epsilon_pos := heps
      epsilon_small := by dsimp only [p]; linarith
      gap := by dsimp only [p]; linarith
      zeta_pos := fun m _ => hzeta m
      zeta_mono := hmono
      zeta_top := by dsimp only [p]; rw [hzetaTop]; linarith
      xi_pos := by intro m hm; dsimp only [xi]; positivity
      xi_beta := ?_
      xi_next := ?_
      rung_next := ?_
      rung_xi := ?_
      xiMin_pos := hxiMin
      xiMin_lower := ?_
      xiMin_attained := ?_
      M_pos := hM
      M_zeta := ?_
      M_xi := hGrid.trans ((min_le_right _ _).trans (min_le_left _ _))
      M_profile := hGrid.trans ((min_le_right _ _).trans (min_le_right _ _))
      M_next := ?_ }
  · intro m hm
    change m.val < N at hm
    change 200 * zeta m.val <= 4 * eps ^ 3 * beta / 25000
    rw [hzetaStep m.val hm]
    have hz := hzetaUpper (m.val + 1) (by omega)
    have hmul := mul_le_mul hqBeta hz (hzeta _).le (by positivity)
    nlinarith [hmul]
  · intro m hm
    change m.val < N at hm
    change 200 * zeta m.val <= eps ^ 2 * beta * zeta (m.val + 1) / 8000
    rw [hzetaStep m.val hm]
    have hh := mul_le_mul_of_nonneg_right hqBeta (hzeta (m.val + 1)).le
    nlinarith
  · intro m hm
    change m < N at hm
    change zeta m <= eps * zeta (m + 1) / 100
    rw [hzetaStep m hm]
    have hh := mul_le_mul_of_nonneg_right hqE (hzeta (m + 1)).le
    nlinarith
  · intro m hm
    change zeta m.val <= (200 * zeta m.val) / 200
    exact le_of_eq (by ring)
  · intro m hm
    change m.val < N at hm
    change 200 * zeta 0 <= 200 * zeta m.val
    gcongr
    exact hmono 0 m.val (Nat.zero_le _) (by omega)
  · refine ⟨⟨0, by omega⟩, by change 0 < N; omega, rfl⟩
  · change (1 : Real) / M <= eps * zeta 0 / 100
    have hh := mul_pos heps (hzeta 0)
    linarith
  · intro m hm
    change m < N at hm
    change (1 : Real) / M <= eps * zeta (m + 1) / 160000
    apply hGridZeta.trans
    gcongr
    exact hmono 0 (m + 1) (Nat.zero_le _) (by omega)

end
end Kakeya.ml1Boot.TrialRestartW94
