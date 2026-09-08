import MyLeanRepo.Kakeya.Streamlined.DividingScales.GridArithmetic

/-!
# Combinatorics of the dividing-scales stopping time

This module contains the finite-order and product-growth facts that are
independent of any cover geometry.  In particular, it has no transition map
or intermediate-cover hypothesis.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Every term of a nondecreasing finite sequence is bounded by its last term. -/
lemma monotoneFin_le_last
    {N : ℕ} {a : Fin (N + 1) → ℝ}
    (hmono : ∀ i : Fin N, a i.castSucc ≤ a i.succ) :
    ∀ i : Fin (N + 1), a i ≤ a (Fin.last N) := by
  have h_induction :
      ∀ m : ℕ, m ≤ N →
        ∀ i : Fin (N + 1), i.val + m = N →
          a i ≤ a (Fin.last N) := by
    intro m hm
    induction m with
    | zero =>
        intro i hi
        have hilast : i = Fin.last N := by
          apply Fin.ext
          simp [Fin.last]
          omega
        rw [hilast]
    | succ m ih =>
        intro i hi
        have hiN : i.val < N := by
          omega
        let j : Fin N := ⟨i.val, hiN⟩
        have hjcast : j.castSucc = i := by
          apply Fin.ext
          rfl
        have hstep : a i ≤ a j.succ := by
          rw [← hjcast]
          exact hmono j
        have hnext : j.succ.val + m = N := by
          dsimp only [j]
          simp
          omega
        exact hstep.trans (ih (by omega) j.succ hnext)
  intro i
  let m := N - i.val
  have hm : m ≤ N := by
    dsimp only [m]
    omega
  have him : i.val + m = N := by
    dsimp only [m]
    omega
  exact h_induction m hm i him

/-- All stopping-time exponents are bounded by the terminal exponent. -/
lemma eta_all_le_terminal
    {N : ℕ} {eta : Fin (N + 1) → ℝ} {epsilon : ℝ}
    (hmono : ∀ i : Fin N, eta i.castSucc ≤ eta i.succ)
    (hterminal : eta (Fin.last N) ≤ epsilon) :
    ∀ i : Fin (N + 1), eta i ≤ epsilon := by
  intro i
  exact (monotoneFin_le_last hmono i).trans hterminal

/--
Generic finite stopping induction.

Starting from level zero, every nonterminal state either finishes in `Good`,
produces a level-indexed `Bad` witness, or advances to the next level.  If a
state reaching the last level is necessarily good, then the process has a
good or bad output.
-/
lemma finite_stopping_dichotomy
    (N : ℕ)
    (State : Fin (N + 1) → Prop)
    (Good : Prop) (Bad : Fin N → Prop)
    (hstart : State 0)
    (hstep :
      ∀ j : Fin N,
        State j.castSucc →
          Good ∨ Bad j ∨ State j.succ)
    (hterminal : State (Fin.last N) → Good) :
    Good ∨ ∃ j : Fin N, Bad j := by
  classical
  by_contra hconclusion
  push Not at hconclusion
  rcases hconclusion with ⟨hnotGood, hnotBad⟩
  let idx (k : ℕ) (hk : k ≤ N) : Fin (N + 1) :=
    ⟨k, Nat.lt_succ_of_le hk⟩
  have hstate :
      ∀ (k : ℕ) (hk : k ≤ N),
        State (idx k hk) := by
    intro k hk
    induction k with
    | zero =>
        convert hstart using 1
        apply Fin.ext
        rfl
    | succ k ih =>
        have hkN : k < N := by omega
        let j : Fin N := ⟨k, hkN⟩
        have hprevious :
            State j.castSucc := by
          convert ih (by omega) using 1
          apply Fin.ext
          rfl
        rcases hstep j hprevious with hgood | hbad | hnext
        · exact (hnotGood hgood).elim
        · exact (hnotBad j hbad).elim
        · convert hnext using 1
          apply Fin.ext
          rfl
  have hlast :
      State (Fin.last N) := by
    convert hstate N le_rfl using 1
    apply Fin.ext
    rfl
  exact hnotGood (hterminal hlast)

/--
If each of `J` scale ratios is at least `delta^(-epsilon^2)` and their
product is at most `1 / delta`, then `J ≤ 1 / epsilon^2`.

This is the numerical termination mechanism in the paper's stopping-time
algorithm.
-/
lemma splitting_termination_bound
    {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta < 1)
    (hepsilon : 0 < epsilon)
    {J : ℕ} (ratio : Fin J → ℝ)
    (hratio :
      ∀ i, delta ^ (-epsilon ^ 2) ≤ ratio i)
    (hproduct :
      ∏ i, ratio i ≤ 1 / delta) :
    (J : ℝ) ≤ 1 / epsilon ^ 2 := by
  have hbase_pos : 0 < delta ^ (-epsilon ^ 2) :=
    Real.rpow_pos_of_pos hdelta _
  have hpow_product :
      (delta ^ (-epsilon ^ 2)) ^ J ≤ ∏ i, ratio i := by
    calc
      (delta ^ (-epsilon ^ 2)) ^ J
          = ∏ _i : Fin J, delta ^ (-epsilon ^ 2) := by
            simp
      _ ≤ ∏ i, ratio i := by
        apply Finset.prod_le_prod
        · intro i _
          exact hbase_pos.le
        · intro i _
          exact hratio i
  have hpow :
      (delta ^ (-epsilon ^ 2)) ^ J ≤ 1 / delta :=
    hpow_product.trans hproduct
  have hpow_eq :
      (delta ^ (-epsilon ^ 2)) ^ J =
        delta ^ (-epsilon ^ 2 * (J : ℝ)) := by
    calc
      (delta ^ (-epsilon ^ 2)) ^ J
          = (delta ^ (-epsilon ^ 2)) ^ (J : ℝ) := by
            rw [Real.rpow_natCast]
      _ = delta ^ (-epsilon ^ 2 * (J : ℝ)) :=
        (Real.rpow_mul hdelta.le _ _).symm
  have hinv_eq : 1 / delta = delta ^ (-1 : ℝ) := by
    simp [Real.rpow_neg_one]
  rw [hpow_eq, hinv_eq] at hpow
  have hlog :=
    Real.log_le_log
      (Real.rpow_pos_of_pos hdelta _)
      hpow
  rw [Real.log_rpow hdelta, Real.log_rpow hdelta] at hlog
  have hlog_delta : Real.log delta < 0 :=
    Real.log_neg hdelta hdelta_one
  have hcoefficient :
      (-1 : ℝ) ≤ -epsilon ^ 2 * (J : ℝ) := by
    by_contra h
    have hstrict :
        -epsilon ^ 2 * (J : ℝ) < -1 := lt_of_not_ge h
    have hreverse :
        (-1 : ℝ) * Real.log delta <
          (-epsilon ^ 2 * (J : ℝ)) * Real.log delta := by
      exact mul_lt_mul_of_neg_right hstrict hlog_delta
    exact (not_lt_of_ge hlog) hreverse
  have hepsilon_sq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hmul : epsilon ^ 2 * (J : ℝ) ≤ 1 := by
    linarith
  calc
    (J : ℝ)
        = (epsilon ^ 2 * (J : ℝ)) / epsilon ^ 2 := by
          field_simp [hepsilon_sq.ne']
    _ ≤ 1 / epsilon ^ 2 := by
      exact div_le_div_of_nonneg_right hmul hepsilon_sq.le

end Kakeya.Streamlined
