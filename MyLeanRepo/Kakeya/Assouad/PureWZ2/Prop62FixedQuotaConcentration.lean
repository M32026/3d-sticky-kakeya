import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62BalancingUnionBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proposition 6.2: concentration for uniform fixed-quota samples

This module supplies the finite hypergeometric estimate needed by the final
exact-balancing step.  It works directly with `Finset.powersetCard`; no
independent Bernoulli replacement is made inside a coarse cell.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem choose_avoidance_scaled
    (N W r : ℕ) (hW : W ≤ N) (hr : r ≤ N) :
    N ^ r * Nat.choose (N - r) W ≤
      (N - W) ^ r * Nat.choose N W := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrN : r < N := by omega
      have hrle : r ≤ N := by omega
      by_cases hWsmall : W ≤ N - (r + 1)
      · have hrec :
            Nat.choose (N - (r + 1)) W * (N - r) =
              Nat.choose (N - r) W * (N - r - W) := by
          have h := Nat.choose_mul_succ_eq (N - (r + 1)) W
          rw [show N - (r + 1) + 1 = N - r by omega] at h
          exact h
        let remainder := N - r - W
        have hN_eq : N = r + W + remainder := by
          dsimp only [remainder]
          omega
        have hNsubW : N - W = r + remainder := by
          dsimp only [remainder]
          omega
        have hNsubr : N - r = W + remainder := by
          dsimp only [remainder]
          omega
        have hNsubrW : N - r - W = remainder := by
          rfl
        have hcross :
            N * (N - r - W) ≤ (N - W) * (N - r) := by
          calc
            N * (N - r - W) = N * remainder := by
              rw [hNsubrW]
            _ = (r + W + remainder) * remainder := by
              rw [hN_eq]
            _ ≤ (r + remainder) * (W + remainder) := by
              nlinarith
            _ = (N - W) * (N - r) := by
              rw [hNsubW, hNsubr]
        have hscaled :
            (N - r) *
                (N ^ (r + 1) *
                  Nat.choose (N - (r + 1)) W) ≤
              (N - r) *
                ((N - W) ^ (r + 1) * Nat.choose N W) := by
          calc
            (N - r) *
                  (N ^ (r + 1) *
                    Nat.choose (N - (r + 1)) W) =
                N ^ (r + 1) *
                  (Nat.choose (N - (r + 1)) W * (N - r)) := by
              ring
            _ =
                N ^ (r + 1) *
                  (Nat.choose (N - r) W * (N - r - W)) := by
              rw [hrec]
            _ =
                N * (N ^ r * Nat.choose (N - r) W) *
                  (N - r - W) := by
              rw [pow_succ]
              ring
            _ ≤
                N * ((N - W) ^ r * Nat.choose N W) *
                  (N - r - W) := by
              exact
                Nat.mul_le_mul_right (N - r - W)
                  (Nat.mul_le_mul_left N (ih hrle))
            _ =
                ((N - W) ^ r * Nat.choose N W) *
                  (N * (N - r - W)) := by
              ring
            _ ≤
                ((N - W) ^ r * Nat.choose N W) *
                  ((N - W) * (N - r)) :=
              Nat.mul_le_mul_left _ hcross
            _ =
                (N - r) *
                  ((N - W) ^ (r + 1) * Nat.choose N W) := by
              rw [pow_succ]
              ring
        exact Nat.le_of_mul_le_mul_left hscaled (by omega)
      · have hzero :
            Nat.choose (N - (r + 1)) W = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hzero]

theorem disjoint_fixedQuota_card
    {α : Type*} [DecidableEq α]
    (available marked : Finset α) (W : ℕ)
    (marked_subset : marked ⊆ available) :
    ((available.powersetCard W).filter fun selected =>
      Disjoint selected marked).card =
      Nat.choose (available.card - marked.card) W := by
  have filterEq :
      (available.powersetCard W).filter
          (fun selected => Disjoint selected marked) =
        (available \ marked).powersetCard W := by
    ext selected
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨selectedSubset, selectedCard⟩, disjoint⟩
      have selectedDiff : selected ⊆ available \ marked := by
        intro x hx
        exact
          Finset.mem_sdiff.mpr
            ⟨selectedSubset hx,
              fun hxm =>
                Finset.disjoint_left.mp disjoint hx hxm⟩
      exact ⟨selectedDiff, selectedCard⟩
    · rintro ⟨selectedSubset, selectedCard⟩
      have selectedAvailable : selected ⊆ available :=
        selectedSubset.trans Finset.sdiff_subset
      have disjoint : Disjoint selected marked := by
        rw [Finset.disjoint_left]
        intro x hxs hxm
        exact
          (Finset.mem_sdiff.mp
            (selectedSubset hxs)).2 hxm
      exact ⟨⟨selectedAvailable, selectedCard⟩, disjoint⟩
  rw [filterEq, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset marked_subset]

lemma exp_neg_inter_card_eq_product
    {α : Type*} [DecidableEq α]
    (marked selected : Finset α) :
    Real.exp (-((selected ∩ marked).card : ℝ)) =
      ∏ i ∈ marked,
        if i ∈ selected then Real.exp (-1) else 1 := by
  have hprod :
      (∏ i ∈ marked,
          if i ∈ selected then Real.exp (-1) else 1) =
        (Real.exp (-1)) ^ (marked ∩ selected).card := by
    rw [← Finset.prod_filter]
    simp only [Finset.filter_mem_eq_inter]
    simp
  rw [hprod, ← Real.exp_nat_mul]
  rw [Finset.inter_comm selected marked]
  congr 1
  ring

lemma product_eq_avoidance_sum
    {α : Type*} [DecidableEq α]
    (marked selected : Finset α) :
    (∏ i ∈ marked,
        if i ∈ selected then Real.exp (-1) else 1) =
      Real.exp (-(marked.card : ℝ)) *
        ∑ witness ∈ marked.powerset,
          if Disjoint selected witness then
            (Real.exp 1 - 1) ^ witness.card
          else 0 := by
  have hfactor :
      ∀ i ∈ marked,
        (if i ∈ selected then Real.exp (-1) else 1) =
          Real.exp (-1) *
            (1 +
              if i ∉ selected then Real.exp 1 - 1 else 0) := by
    intro i hi
    by_cases his : i ∈ selected
    · simp [his, Real.exp_neg]
    · simp [his, Real.exp_neg]
  rw [Finset.prod_congr rfl hfactor,
    Finset.prod_mul_distrib]
  have hconst :
      (∏ _i ∈ marked, Real.exp (-1)) =
        Real.exp (-(marked.card : ℝ)) := by
    rw [Finset.prod_const]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hconst, Finset.prod_one_add]
  congr 1
  apply Finset.sum_congr rfl
  intro witness witnessMem
  by_cases hdisj : Disjoint selected witness
  · rw [if_pos hdisj]
    have hall : ∀ i ∈ witness, i ∉ selected := by
      intro i hi
      exact fun his =>
        Finset.disjoint_left.mp hdisj his hi
    apply Finset.prod_eq_pow_card
    intro i hi
    simp [hall i hi]
  · rw [if_neg hdisj]
    rw [Finset.not_disjoint_iff] at hdisj
    rcases hdisj with ⟨i, his, hiw⟩
    have hzero :
        (if i ∉ selected then Real.exp 1 - 1 else 0) = 0 := by
      simp [his]
    exact Finset.prod_eq_zero hiw hzero

lemma fixedQuota_avoidance_ratio
    (N W r : ℕ)
    (hN : 0 < N) (hW : W ≤ N) (hr : r ≤ N) :
    (Nat.choose (N - r) W : ℝ) ≤
      (Nat.choose N W : ℝ) *
        (((N - W : ℕ) : ℝ) / N) ^ r := by
  have hscaledNat :=
    choose_avoidance_scaled N W r hW hr
  have hscaled :
      (N : ℝ) ^ r *
          (Nat.choose (N - r) W : ℝ) ≤
        ((N - W : ℕ) : ℝ) ^ r *
          (Nat.choose N W : ℝ) := by
    exact_mod_cast hscaledNat
  have hpow : 0 < (N : ℝ) ^ r :=
    pow_pos (by exact_mod_cast hN) r
  calc
    (Nat.choose (N - r) W : ℝ) ≤
        (((N - W : ℕ) : ℝ) ^ r *
            (Nat.choose N W : ℝ)) /
          (N : ℝ) ^ r := by
      apply (le_div_iff₀ hpow).2
      simpa [mul_comm] using hscaled
    _ =
        (Nat.choose N W : ℝ) *
          (((N - W : ℕ) : ℝ) / N) ^ r := by
      rw [div_pow]
      field_simp [show (N : ℝ) ≠ 0 by
        exact_mod_cast hN.ne']

theorem fixedQuota_exp_neg_sum_le
    {α : Type*} [DecidableEq α]
    (available marked : Finset α) (W : ℕ)
    (marked_subset : marked ⊆ available)
    (W_le : W ≤ available.card)
    (available_pos : 0 < available.card) :
    (∑ selected ∈ available.powersetCard W,
        Real.exp (-((selected ∩ marked).card : ℝ))) ≤
      (Nat.choose available.card W : ℝ) *
        Real.exp (-(3 / 5 : ℝ) *
          ((W : ℝ) / available.card) * marked.card) := by
  let u : ℝ := Real.exp 1 - 1
  let q : ℝ :=
    ((available.card - W : ℕ) : ℝ) / available.card
  have u_nonneg : 0 ≤ u := by
    dsimp only [u]
    linarith [Real.exp_one_gt_two]
  have q_nonneg : 0 ≤ q := by
    positivity
  have expansion :
      (∑ selected ∈ available.powersetCard W,
          Real.exp (-((selected ∩ marked).card : ℝ))) =
        Real.exp (-(marked.card : ℝ)) *
          ∑ witness ∈ marked.powerset,
            u ^ witness.card *
              Nat.choose
                (available.card - witness.card) W := by
    calc
      (∑ selected ∈ available.powersetCard W,
          Real.exp (-((selected ∩ marked).card : ℝ))) =
          ∑ selected ∈ available.powersetCard W,
            Real.exp (-(marked.card : ℝ)) *
              ∑ witness ∈ marked.powerset,
                if Disjoint selected witness then
                  u ^ witness.card
                else 0 := by
        apply Finset.sum_congr rfl
        intro selected selectedMem
        calc
          Real.exp (-((selected ∩ marked).card : ℝ)) =
              ∏ i ∈ marked,
                if i ∈ selected then
                  Real.exp (-1)
                else 1 :=
            exp_neg_inter_card_eq_product marked selected
          _ =
              Real.exp (-(marked.card : ℝ)) *
                ∑ witness ∈ marked.powerset,
                  if Disjoint selected witness then
                    u ^ witness.card
                  else 0 := by
            simpa [u] using
              product_eq_avoidance_sum marked selected
      _ =
          Real.exp (-(marked.card : ℝ)) *
            ∑ selected ∈ available.powersetCard W,
              ∑ witness ∈ marked.powerset,
                if Disjoint selected witness then
                  u ^ witness.card
                else 0 := by
        rw [Finset.mul_sum]
      _ =
          Real.exp (-(marked.card : ℝ)) *
            ∑ witness ∈ marked.powerset,
              ∑ selected ∈ available.powersetCard W,
                if Disjoint selected witness then
                  u ^ witness.card
                else 0 := by
        congr 1
        rw [Finset.sum_comm]
      _ =
          Real.exp (-(marked.card : ℝ)) *
            ∑ witness ∈ marked.powerset,
              u ^ witness.card *
                Nat.choose
                  (available.card - witness.card) W := by
        congr 1
        apply Finset.sum_congr rfl
        intro witness witnessMem
        have witnessSubset : witness ⊆ available :=
          (Finset.mem_powerset.mp witnessMem).trans
            marked_subset
        calc
          (∑ selected ∈ available.powersetCard W,
              if Disjoint selected witness then
                u ^ witness.card
              else 0) =
              ∑ selected ∈
                  (available.powersetCard W).filter
                    (fun selected =>
                      Disjoint selected witness),
                u ^ witness.card := by
            rw [Finset.sum_filter]
          _ =
              u ^ witness.card *
                (((available.powersetCard W).filter
                  fun selected =>
                    Disjoint selected witness).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
          _ =
              u ^ witness.card *
                Nat.choose
                  (available.card - witness.card) W := by
            rw [disjoint_fixedQuota_card
              available witness W witnessSubset]
  rw [expansion]
  have chooseBound :
      ∀ witness ∈ marked.powerset,
        (Nat.choose
            (available.card - witness.card) W : ℝ) ≤
          (Nat.choose available.card W : ℝ) *
            q ^ witness.card := by
    intro witness witnessMem
    apply fixedQuota_avoidance_ratio
    · exact available_pos
    · exact W_le
    · exact
        Finset.card_le_card <|
          (Finset.mem_powerset.mp witnessMem).trans
            marked_subset
  calc
    Real.exp (-(marked.card : ℝ)) *
        ∑ witness ∈ marked.powerset,
          u ^ witness.card *
            Nat.choose
              (available.card - witness.card) W ≤
      Real.exp (-(marked.card : ℝ)) *
        ∑ witness ∈ marked.powerset,
          u ^ witness.card *
            ((Nat.choose available.card W : ℝ) *
              q ^ witness.card) := by
      gcongr with witness witnessMem
      exact chooseBound witness witnessMem
    _ =
        (Nat.choose available.card W : ℝ) *
          (Real.exp (-1) * (1 + u * q)) ^
            marked.card := by
      have powersetSum :
          (∑ witness ∈ marked.powerset,
              u ^ witness.card * q ^ witness.card) =
            (1 + u * q) ^ marked.card := by
        calc
          (∑ witness ∈ marked.powerset,
              u ^ witness.card * q ^ witness.card) =
              ∑ witness ∈ marked.powerset,
                (u * q) ^ witness.card := by
            apply Finset.sum_congr rfl
            intro witness witnessMem
            rw [mul_pow]
          _ = ∏ _i ∈ marked, (1 + u * q) := by
            rw [Finset.prod_one_add]
            apply Finset.sum_congr rfl
            intro witness witnessMem
            exact
              (Finset.prod_eq_pow_card
                fun _ _ => rfl).symm
          _ = (1 + u * q) ^ marked.card := by
            simp
      have factorSum :
          (∑ witness ∈ marked.powerset,
              u ^ witness.card *
                ((Nat.choose available.card W : ℝ) *
                  q ^ witness.card)) =
            (Nat.choose available.card W : ℝ) *
              ∑ witness ∈ marked.powerset,
                u ^ witness.card * q ^ witness.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro witness witnessMem
        ring
      rw [factorSum, powersetSum]
      have expPower :
          Real.exp (-(marked.card : ℝ)) =
            (Real.exp (-1)) ^ marked.card := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [expPower]
      calc
        (Real.exp (-1)) ^ marked.card *
              ((Nat.choose available.card W : ℝ) *
                (1 + u * q) ^ marked.card) =
            (Nat.choose available.card W : ℝ) *
              ((Real.exp (-1)) ^ marked.card *
                (1 + u * q) ^ marked.card) := by
          ring
        _ =
            (Nat.choose available.card W : ℝ) *
              (Real.exp (-1) * (1 + u * q)) ^
                marked.card := by
          rw [mul_pow]
    _ =
        (Nat.choose available.card W : ℝ) *
          (1 - ((W : ℝ) / available.card) *
            (1 - Real.exp (-1))) ^ marked.card := by
      congr 1
      congr 1
      dsimp only [u, q]
      have availableNe :
          (available.card : ℝ) ≠ 0 := by
        exact_mod_cast available_pos.ne'
      have castSub :
          ((available.card - W : ℕ) : ℝ) =
            (available.card : ℝ) - W :=
        Nat.cast_sub W_le
      rw [castSub, Real.exp_neg]
      field_simp [availableNe, (Real.exp_pos 1).ne']
      ring
    _ ≤
        (Nat.choose available.card W : ℝ) *
          Real.exp (-((W : ℝ) / available.card) *
            (1 - Real.exp (-1)) * marked.card) := by
      gcongr
      have xNonneg :
          0 ≤ ((W : ℝ) / available.card) *
            (1 - Real.exp (-1)) := by
        have expLe : Real.exp (-1) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by norm_num)
        exact
          mul_nonneg (by positivity)
            (sub_nonneg.mpr expLe)
      have xLe :
          ((W : ℝ) / available.card) *
              (1 - Real.exp (-1)) ≤ 1 := by
        have ratioLe :
            (W : ℝ) / available.card ≤ 1 := by
          exact
            (div_le_one
              (by exact_mod_cast available_pos)).2
                (by exact_mod_cast W_le)
        have expNonneg : 0 ≤ Real.exp (-1) :=
          (Real.exp_pos _).le
        have factorLe :
            1 - Real.exp (-1) ≤ 1 := by
          linarith
        have factorNonneg :
            0 ≤ 1 - Real.exp (-1) := by
          exact
            sub_nonneg.mpr
              (Real.exp_le_one_iff.mpr (by norm_num))
        exact
          (mul_le_mul ratioLe factorLe
            factorNonneg (by positivity)).trans_eq
              (mul_one _)
      have baseLe :
          1 - ((W : ℝ) / available.card) *
              (1 - Real.exp (-1)) ≤
            Real.exp
              (-((W : ℝ) / available.card) *
                (1 - Real.exp (-1))) := by
        linarith [Real.add_one_le_exp
          (-((W : ℝ) / available.card) *
            (1 - Real.exp (-1)))]
      calc
        (1 - ((W : ℝ) / available.card) *
              (1 - Real.exp (-1))) ^ marked.card ≤
            Real.exp
              (-((W : ℝ) / available.card) *
                (1 - Real.exp (-1))) ^ marked.card := by
          exact
            pow_le_pow_left₀ (by linarith) baseLe _
        _ =
            Real.exp
              (-((W : ℝ) / available.card) *
                (1 - Real.exp (-1)) *
                  marked.card) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    _ ≤
        (Nat.choose available.card W : ℝ) *
          Real.exp (-(3 / 5 : ℝ) *
            ((W : ℝ) / available.card) *
              marked.card) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        have expNegLt :
            Real.exp (-1) < (2 / 5 : ℝ) :=
          Real.exp_neg_one_lt_d9.trans_le (by norm_num)
        have factorLower :
            (3 / 5 : ℝ) ≤ 1 - Real.exp (-1) := by
          linarith
        have ratioNonneg :
            0 ≤ (W : ℝ) / available.card := by
          positivity
        have cardNonneg :
            0 ≤ (marked.card : ℝ) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            factorLower ratioNonneg) cardNonneg]
      · positivity

end Kakeya.Assouad

end
