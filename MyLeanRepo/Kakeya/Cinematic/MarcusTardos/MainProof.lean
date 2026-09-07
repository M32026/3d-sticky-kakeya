import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.IntersectionCounting
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.WeightOptimization
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.FinalAssembly
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.TheoremWiring
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.WeightedLowerBound
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.LeaderPairs
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.ConcreteBlockSum
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Statements
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DirectBoundFramework
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.SingularPairBound
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GoodContributionHyp
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Main proof of Marcus-Tardos Theorem 1

Wires together all components:
- ConcreteBlockSum (diagonal bound for dyadic blocks)
- Weighted lower bound (Lemma 4)
- Leader pair upper bound (Lemma 5)
- Direct singular-pair bound (telescoping Cauchy-Schwarz)
- Intersection counting (Lemma 3)
- Weight optimization
- Final assembly
- Theorem wiring

## Whiteprint node
- `MainProof`
-/

namespace MarcusTardos.MainProof

open MarcusTardos WeightOptimization FinalAssembly WeightedLowerBound LeaderPairs

variable {α : Type*} [DecidableEq α]

/-! ### Block order sum G -/

/-- Block order sum for sequence `i`: wrapper around `ConcreteBlockSum.G`. -/
noncomputable def G {m : ℕ} (A : Fin m → List α) (i : Fin m) (l : ℕ) (a b : α) : ℝ :=
  ConcreteBlockSum.G (A i) l a b

/-- `G` with natural-number index for `WeightedLowerBound`. -/
noncomputable def G_nat {m : ℕ} (A : Fin m → List α) (i : ℕ) (l : ℕ) (a b : α) : ℝ :=
  if h : i < m then G A (⟨i, h⟩ : Fin m) l a b else 0

/-- Weighted sum `S^{ij}` for `Fin m` indices. -/
noncomputable def S {m : ℕ} (A : Fin m → List α) (k : ℕ) (w : ℕ → ℝ)
    (alphabet : Finset α) (i j : Fin m) : ℝ :=
  WeightedLowerBound.S k w alphabet (G_nat A) i.val j.val

/-! ### Direct upper bound on S^{ij} -/

/--
Direct upper bound on `S^{ij}` for a pair of cyclically IR sequences.

Uses the telescoping Cauchy-Schwarz bound:
  `S^{ij} ≤ p_{ij} * W - p_{ij}^2 / (12 * V)`
-/
lemma direct_S_bound {m d n : ℕ} {alphabet : Finset α} {A : Fin m → List α}
    (hnodup : ∀ i, (A i).Nodup)
    (hlen : ∀ i, (A i).length = d)
    (halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet)
    (hir : ∀ i j, i ≠ j → IsCyclicIntersectionReverse (A i) (A j))
    (k : ℕ) (hk : 2^k ≥ d) (w : ℕ → ℝ) (hw_pos : ∀ l ∈ Finset.Icc 1 k, 0 < w l)
    (i j : Fin m) (hne : i ≠ j) :
    S A k w alphabet i j ≤
    (pairIntersection A i j : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
    (pairIntersection A i j : ℝ)^2 / (12 * ∑ l ∈ Finset.Icc 1 k, 1 / w l) := by
  classical
  by_cases hk0 : k = 0
  · -- k = 0 case: both sides are 0
    simp [S, G_nat, WeightedLowerBound.S, hk0, Finset.sum_eq_zero]
    <;> norm_num
  · -- k > 0 case
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    let Ai := A i
    let Bj := A j
    have hA : Ai.Nodup := hnodup i
    have hB : Bj.Nodup := hnodup j
    have hlenA : Ai.length = d := hlen i
    have hlenB : Bj.length = d := hlen j
    have hcir : IsCyclicIntersectionReverse Ai Bj := hir i j hne
    have h_good : DirectBoundFramework.GoodContributionHyp Ai Bj :=
      GoodContributionHyp.good_contribution_hyp hA hB hcir
    have h_singular : DirectBoundFramework.SingularCountHyp Ai Bj 1 := by
      intro l hl
      have h_main := SingularPairBound.at_most_one_singular_pair hA hB hcir l
      rcases h_main with ⟨st0, hst0⟩
      have h_sub : DirectBoundFramework.singularPairs Ai Bj l ⊆ {st0} := by
        intro st hst
        have h1 : st ∈ DirectBoundFramework.allPairs l := (Finset.mem_filter.mp hst).1
        have h3 : ¬DirectBoundFramework.isPairIR Ai Bj st := (Finset.mem_filter.mp hst).2.2
        have h1' : st.1 ∈ binaryStrings l ∧ st.2 ∈ binaryStrings l := by
          simpa [DirectBoundFramework.allPairs, Finset.mem_product] using h1
        have h4 : st.1.length = l := binaryStrings_mem.mp h1'.1
        have h5 : st.2.length = l := binaryStrings_mem.mp h1'.2
        have h3' : ¬ IsIntersectionReverse (block Ai st.1) (block Bj st.2) :=
          show ¬ DirectBoundFramework.isPairIR Ai Bj st from h3
        have h_eq : st = st0 := hst0 st.1 st.2 h4 h5 h3'
        exact Finset.mem_singleton.mpr h_eq
      have h_card : (DirectBoundFramework.singularPairs Ai Bj l).card ≤ 1 := by
        have h : (DirectBoundFramework.singularPairs Ai Bj l).card ≤ ({st0} : Finset (List Bool × List Bool)).card :=
          Finset.card_le_card h_sub
        have h1 : ({st0} : Finset (List Bool × List Bool)).card = 1 := by simp
        rw [h1] at h
        exact h
      exact h_card
    have h_main := DirectBoundFramework.direct_bound_with_assumptions
      (d := d) (A := Ai) (B := Bj)
      hA hB hlenA hlenB alphabet (halph i) (halph j)
      k hk_pos hk w hw_pos 1 (by norm_num) h_good h_singular
    have hV_pos : 0 < ∑ l ∈ Finset.Icc 1 k, 1 / w l := by
      apply Finset.sum_pos
      · intro l hl; exact one_div_pos.mpr (hw_pos l hl)
      · have h1 : 1 ≤ k := by linarith
        have h_ne : (Finset.Icc 1 k).Nonempty := Finset.nonempty_Icc.mpr h1
        exact h_ne
    set V : ℝ := ∑ l ∈ Finset.Icc 1 k, 1 / w l with hV
    have h_p_nonneg : 0 ≤ (pairIntersection A i j : ℝ) := by positivity
    have h4V_le_12V : (4 : ℝ) * V ≤ (12 : ℝ) * V := by
      have hV_nonneg : 0 ≤ V := hV_pos.le
      nlinarith
    have h4_pos : 0 < (4 : ℝ) * V := by positivity
    have h_p2_nonneg : 0 ≤ (pairIntersection A i j : ℝ)^2 := by positivity
    have h12_pos : 0 < (12 : ℝ) * V := by positivity
    have h_ineq : (pairIntersection A i j : ℝ)^2 / ((12 : ℝ) * V) ≤
        (pairIntersection A i j : ℝ)^2 / ((4 : ℝ) * V) := by
      set p := (pairIntersection A i j : ℝ) with hp
      have h_mul : p^2 * ((4 : ℝ) * V) ≤ p^2 * ((12 : ℝ) * V) := by
        gcongr <;> linarith
      calc
        p^2 / ((12 : ℝ) * V)
          = (p^2 * ((4 : ℝ) * V)) / (((12 : ℝ) * V) * ((4 : ℝ) * V)) := by
            field_simp [h4_pos.ne', h12_pos.ne'] <;> ring
        _ ≤ (p^2 * ((12 : ℝ) * V)) / (((12 : ℝ) * V) * ((4 : ℝ) * V)) := by gcongr
        _ = p^2 / ((4 : ℝ) * V) := by
            field_simp [h4_pos.ne', h12_pos.ne'] <;> ring
    dsimp only at h_main
    have h_p_eq : (pairIntersection A i j : ℝ) = ((Ai.toFinset ∩ Bj.toFinset).card : ℝ) := by
      rfl
    have h_eqS : S A k w alphabet i j =
        ∑ l ∈ Finset.Icc 1 k, w l *
          (∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
            ConcreteBlockSum.G Ai l a b * ConcreteBlockSum.G Bj l a b) := by
      simp [S, G_nat, G, WeightedLowerBound.S]
      <;> congr <;> funext l a b <;> simp [G_nat, G] <;> aesop
    have h_main' : S A k w alphabet i j ≤
        ((Ai.toFinset ∩ Bj.toFinset).card : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
        ((Ai.toFinset ∩ Bj.toFinset).card : ℝ)^2 / ((4 : ℝ) * V) := by
      have h_goal4 : ((4 * (1 : ℝ) * V)) = (4 : ℝ) * V := by ring
      convert h_main using 2 <;> ring
    have h_final : S A k w alphabet i j ≤
        (pairIntersection A i j : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
        (pairIntersection A i j : ℝ)^2 / ((4 : ℝ) * V) := by
      rw [h_p_eq]
      exact h_main'
    have h_goal : S A k w alphabet i j ≤
        (pairIntersection A i j : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
        (pairIntersection A i j : ℝ)^2 / ((12 : ℝ) * V) := by
      calc
        S A k w alphabet i j
          ≤ (pairIntersection A i j : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
            (pairIntersection A i j : ℝ)^2 / ((4 : ℝ) * V) := h_final
        _ ≤ (pairIntersection A i j : ℝ) * (∑ l ∈ Finset.Icc 1 k, w l) -
            (pairIntersection A i j : ℝ)^2 / ((12 : ℝ) * V) := by
              exact sub_le_sub_left h_ineq _
    exact h_goal

/-! ### Sum equivalence helper -/

/-- Convert double sum over `range m` with erase to off-diagonal sum over `Fin m`. -/
private lemma sum_range_offDiag_eq_fin {m : ℕ} (hm : 0 < m) {f : ℕ → ℕ → ℝ} :
    ∑ i ∈ Finset.range m, ∑ j ∈ (Finset.range m).erase i, f i j =
    ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)), f ij.1.val ij.2.val := by
  have h_step1 : ∀ (s : Finset ℕ),
      ∑ i ∈ s, ∑ j ∈ s.erase i, f i j = ∑ p ∈ Finset.offDiag s, f p.1 p.2 := by
    intro s
    have h_off : Finset.offDiag s = (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 ≠ p.2) := by
      ext ⟨x, y⟩
      simp [Finset.mem_offDiag] <;> tauto
    rw [h_off]
    have h_eq1 : ∑ i ∈ s, ∑ j ∈ s.erase i, f i j =
        ∑ p ∈ s ×ˢ s, (if p.1 ≠ p.2 then f p.1 p.2 else 0) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _
      have h2 : ∑ j ∈ s.erase i, f i j = ∑ j ∈ s, (if i ≠ j then f i j else 0) := by
        have h21 : s.filter (fun j => i ≠ j) = s.erase i := by
          ext x
          simp [Finset.mem_erase]
          <;> tauto
        have h_eq : ∑ j ∈ s, (if i ≠ j then f i j else 0) =
            ∑ j ∈ s.filter (fun j => i ≠ j), f i j + ∑ j ∈ s.filter (fun j => ¬(i ≠ j)), (0 : ℝ) := by
          rw [Finset.sum_ite]
        rw [h_eq, h21]
        <;> simp
      rw [h2]
    rw [h_eq1, Finset.sum_filter]
    <;> rfl
  have h1 := h_step1 (Finset.range m)
  rw [h1]
  let e : ℕ × ℕ → Fin m × Fin m := fun p =>
    (⟨p.1 % m, Nat.mod_lt p.1 hm⟩, ⟨p.2 % m, Nat.mod_lt p.2 hm⟩)
  let g : Fin m × Fin m → ℕ × ℕ := fun q => (q.1.val, q.2.val)
  have h_hi : ∀ (p : ℕ × ℕ), p ∈ Finset.offDiag (Finset.range m) → e p ∈ Finset.offDiag (Finset.univ : Finset (Fin m)) := by
    intro p hp
    have h1 : p.1 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).1
    have h2 : p.2 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).2.1
    have h3 : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have h4 : p.1 < m := Finset.mem_range.mp h1
    have h5 : p.2 < m := Finset.mem_range.mp h2
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    <;> simp [e, h4, h5, h3, Nat.mod_eq_of_lt] <;> omega
  have h_hj : ∀ (q : Fin m × Fin m), q ∈ Finset.offDiag (Finset.univ : Finset (Fin m)) → g q ∈ Finset.offDiag (Finset.range m) := by
    intro q hq
    have h3 : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hq).2.2
    have h3' : (q.1 : ℕ) ≠ (q.2 : ℕ) := by
      intro h
      apply h3
      exact Fin.ext h
    simp only [g, Finset.mem_offDiag, Finset.mem_range]
    <;> exact ⟨Fin.is_lt q.1, Fin.is_lt q.2, h3'⟩
  have h_left : ∀ (p : ℕ × ℕ), p ∈ Finset.offDiag (Finset.range m) → g (e p) = p := by
    intro p hp
    have h1 : p.1 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).1
    have h2 : p.2 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).2.1
    have h4 : p.1 < m := Finset.mem_range.mp h1
    have h5 : p.2 < m := Finset.mem_range.mp h2
    simp [e, g, h4, h5, Nat.mod_eq_of_lt] <;> ext <;> simp
  have h_right : ∀ (q : Fin m × Fin m), q ∈ Finset.offDiag (Finset.univ : Finset (Fin m)) → e (g q) = q := by
    intro q _
    simp [e, g, Nat.mod_eq_of_lt] <;> ext <;> simp
  have h_eq : ∀ (p : ℕ × ℕ), p ∈ Finset.offDiag (Finset.range m) →
      f p.1 p.2 = f (e p).1.val (e p).2.val := by
    intro p hp
    have h1 : p.1 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).1
    have h2 : p.2 ∈ Finset.range m := (Finset.mem_offDiag.mp hp).2.1
    have h4 : p.1 < m := Finset.mem_range.mp h1
    have h5 : p.2 < m := Finset.mem_range.mp h2
    have h6 : (e p).1.val = p.1 := by simp [e, h4, Nat.mod_eq_of_lt]
    have h7 : (e p).2.val = p.2 := by simp [e, h5, Nat.mod_eq_of_lt]
    rw [h6, h7]
  exact Finset.sum_nbij' (s := Finset.offDiag (Finset.range m))
    (t := Finset.offDiag (Finset.univ : Finset (Fin m)))
    (i := e) (j := g) h_hi h_hj h_left h_right h_eq

/-! ### Main proof core -/

/-- Core proof of the equal-length bound for fixed `α`, `m`, `d`, `n`. -/
private lemma main_proof_core (α : Type) [DecidableEq α] (m d n : ℕ) (hm : 0 < m)
    (alphabet : Finset α) (hcard : alphabet.card = n)
    (A : Fin m → List α)
    (hnodup' : ∀ i, (A i).Nodup ∧ (A i).length = d)
    (halph' : ∀ i, ∀ x ∈ A i, x ∈ alphabet)
    (hir : ∀ i j, i ≠ j → IsCyclicIntersectionReverse (A i) (A j)) :
    (d : ℝ) ≤ 64 * (Real.sqrt n * Real.log (n + 1) + n / Real.sqrt m) := by
  have hnodup : ∀ i, (A i).Nodup := fun i => (hnodup' i).1
  have hlen : ∀ i, (A i).length = d := fun i => (hnodup' i).2
  have halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet := halph'
  by_cases hn0 : n = 0
  · -- n = 0 implies alphabet empty, all sequences empty, d = 0
    have h_alph_empty : alphabet = ∅ := by
      simpa [Finset.card_eq_zero] using hcard.trans hn0
    let i0 : Fin m := ⟨0, hm⟩
    have h' : ∀ x, x ∉ A i0 := by
      intro x hx
      have h_in_alph : x ∈ alphabet := halph i0 x hx
      rw [h_alph_empty] at h_in_alph
      simpa using h_in_alph
    have hA_empty : A i0 = [] := by
      by_cases h : A i0 = []
      · exact h
      · have h_exists : ∃ x, x ∈ A i0 := List.exists_mem_of_ne_nil (A i0) h
        rcases h_exists with ⟨x, hx⟩
        exact False.elim (h' x hx)
    have h_len : (A i0).length = d := hlen i0
    have h_d0 : d = 0 := by
      rw [hA_empty] at h_len
      exact h_len.symm
    have h_goal : (d : ℝ) ≤ 64 * (Real.sqrt n * Real.log (n + 1) + n / Real.sqrt m) := by
      rw [h_d0, hn0]
      <;> simp <;> norm_num
    exact h_goal
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hd : d ≤ 1
    · -- d ≤ 1, bound is trivial since RHS > 1 for n ≥ 1
      have h_n1 : 1 ≤ n := by omega
      have h1 : Real.log 2 ≤ Real.log (n + 1) := by
        have h11 : (0 : ℝ) < 2 := by norm_num
        have h12 : (2 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (by omega)
        exact Real.log_le_log h11 h12
      have h2 : Real.sqrt n ≥ 1 := by
        have h3 : (n : ℝ) ≥ 1 := by exact_mod_cast h_n1
        have h4 : Real.sqrt n ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h3
        simpa using h4
      have h_log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h5 : Real.sqrt n * Real.log (n + 1) ≥ (0.6931471803 : ℝ) := by
        have h6 : Real.sqrt n * Real.log (n + 1) ≥ 1 * Real.log 2 := by
          have h61 : Real.sqrt n ≥ 1 := h2
          have h62 : Real.log (n + 1) ≥ Real.log 2 := h1
          nlinarith
        have h7 : (1 : ℝ) * Real.log 2 > (0.6931471803 : ℝ) := by
          have h8 : (0.6931471803 : ℝ) < Real.log 2 := h_log2_gt
          linarith
        linarith
      have h6 : 0 ≤ n / Real.sqrt m := by positivity
      have h7 : (d : ℝ) ≤ 1 := by exact_mod_cast hd
      have h8 : 64 * (Real.sqrt n * Real.log (n + 1) + n / Real.sqrt m) ≥ 1 := by
        have h9 : 64 * (Real.sqrt n * Real.log (n + 1) + n / Real.sqrt m) ≥ 64 * (0.6931471803 : ℝ) := by
          gcongr
          <;> linarith
        have h10 : 64 * (0.6931471803 : ℝ) > 1 := by norm_num
        linarith
      linarith
    · -- d > 1, main proof
      have h_gt1 : 1 < d := by omega
      set k : ℕ := Nat.clog 2 d with hk
      set p : ℕ := totalIntersection A with hp
      let w : ℕ → ℝ := fun l => WeightOptimization.w k l
      set W : ℝ := ∑ l ∈ Finset.Icc 1 k, w l with hW_def
      set V : ℝ := ∑ l ∈ Finset.Icc 1 k, 1 / w l with hV_def
      set U : ℝ := ∑ l ∈ Finset.Icc 1 k, w l / (2 : ℝ)^l with hU_def
      have hw_pos : ∀ l ∈ Finset.Icc 1 k, 0 < w l := fun l _ => w_pos k l
      have hw_nonneg : ∀ l ∈ Finset.Icc 1 k, 0 ≤ w l := fun l hl => (hw_pos l hl).le
      have hk_pos : 0 < k := Nat.clog_pos (by norm_num) h_gt1
      have hG_bound : ∀ i ∈ Finset.range m, ∀ l ∈ Finset.Icc 1 k,
          ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (G_nat A i l a b)^2 ≤
          (d : ℝ)^2 / (2 : ℝ)^l := by
        intro i hi l hl
        have h_i_lt : i < m := Finset.mem_range.mp hi
        let i' : Fin m := ⟨i, h_i_lt⟩
        have h_eq : G_nat A i l = G A i' l := by
          funext a b
          simp [G_nat, h_i_lt] <;> rfl
        rw [h_eq]
        exact ConcreteBlockSum.diagonal_bound_concrete (hnodup i') d (hlen i') (halph i') l
      have h_lower : ∑ i ∈ Finset.range m, ∑ j ∈ (Finset.range m).erase i,
          WeightedLowerBound.S k w alphabet (G_nat A) i j ≥
          - (m : ℝ) * (d : ℝ)^2 * U :=
        weighted_lower_bound m k d w alphabet (G_nat A) hw_nonneg hG_bound
      let offDiag := Finset.offDiag (Finset.univ : Finset (Fin m))
      have h_sum_equiv : ∑ i ∈ Finset.range m, ∑ j ∈ (Finset.range m).erase i,
          WeightedLowerBound.S k w alphabet (G_nat A) i j =
          ∑ ij ∈ offDiag, S A k w alphabet ij.1 ij.2 := by
        simp only [S]
        have h1 : ∑ i ∈ Finset.range m, ∑ j ∈ (Finset.range m).erase i,
            WeightedLowerBound.S k w alphabet (G_nat A) i j =
            ∑ ij ∈ offDiag,
              WeightedLowerBound.S k w alphabet (G_nat A) ij.1.val ij.2.val :=
          sum_range_offDiag_eq_fin hm
        rw [h1]
        <;> rfl
      rw [h_sum_equiv] at h_lower
      have h_upper_each : ∀ ij ∈ offDiag,
          S A k w alphabet ij.1 ij.2 ≤
          (pairIntersection A ij.1 ij.2 : ℝ) * W -
          (pairIntersection A ij.1 ij.2 : ℝ)^2 / (12 * V) := by
        intro ij hij
        let i := ij.1
        let j := ij.2
        have hne : i ≠ j := (Finset.mem_offDiag.mp hij).2.2
        have h_k_ge : 2^k ≥ d := by
          rw [hk]
          exact Nat.le_pow_clog (by norm_num) d
        exact direct_S_bound (n := n) hnodup hlen halph hir k h_k_ge w hw_pos i j hne
      let f : (Fin m × Fin m) → ℝ := fun ij => (pairIntersection A ij.1 ij.2 : ℝ)
      have h_sum_p : ∑ ij ∈ offDiag, f ij = (p : ℝ) := by
        have h_total : (totalIntersection A : ℝ) = ∑ ij ∈ offDiag, f ij := by
          simp [totalIntersection, offDiag, f]
          <;> rfl
        exact h_total.symm.trans (by exact_mod_cast hp)
      have h_sum_upper : ∑ ij ∈ offDiag, S A k w alphabet ij.1 ij.2 ≤
          W * (p : ℝ) - (1 / (12 * V)) * ∑ ij ∈ offDiag, f ij^2 := by
        calc
          ∑ ij ∈ offDiag, S A k w alphabet ij.1 ij.2
            ≤ ∑ ij ∈ offDiag, (f ij * W - f ij^2 / (12 * V)) := by
              apply Finset.sum_le_sum
              intro ij hij
              exact h_upper_each ij hij
          _ = W * ∑ ij ∈ offDiag, f ij - (1 / (12 * V)) * ∑ ij ∈ offDiag, f ij^2 := by
              have h_sum1 : ∑ ij ∈ offDiag, (f ij * W) = W * ∑ ij ∈ offDiag, f ij := by
                have h_comm : ∑ ij ∈ offDiag, (f ij * W) = ∑ ij ∈ offDiag, (W * f ij) := by
                  apply Finset.sum_congr rfl
                  intro _ _
                  <;> ring
                rw [h_comm, Finset.mul_sum]
              have h_sum2 : ∑ ij ∈ offDiag, (f ij^2 / (12 * V)) =
                  (1 / (12 * V)) * ∑ ij ∈ offDiag, f ij^2 := by
                have h_div : (∑ ij ∈ offDiag, f ij^2) / (12 * V) = ∑ ij ∈ offDiag, (f ij^2 / (12 * V)) :=
                  Finset.sum_div offDiag (fun ij => f ij^2) (12 * V)
                exact h_div.symm ▸ by ring
              rw [Finset.sum_sub_distrib, h_sum1, h_sum2]
          _ = W * (p : ℝ) - (1 / (12 * V)) * ∑ ij ∈ offDiag, f ij^2 := by
              rw [h_sum_p] <;> ring
      have h_card : offDiag.card ≤ m^2 := by
        have h1 : offDiag.card = m * m - m := by
          rw [Finset.offDiag_card, Finset.card_fin]
          <;> omega
        rw [h1]
        have h4 : m * m = m^2 := by ring
        rw [h4]
        exact Nat.sub_le (m^2) m
      have h_cs : (p : ℝ)^2 ≤ (offDiag.card : ℝ) * ∑ ij ∈ offDiag, f ij^2 := by
        have h_cs' := sq_sum_le_card_mul_sum_sq (s := offDiag) (f := f)
        rw [h_sum_p] at h_cs'
        exact h_cs'
      have h_p_sq : (p : ℝ)^2 ≤ (m : ℝ)^2 * ∑ ij ∈ offDiag, f ij^2 := by
        have h9 : (offDiag.card : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast h_card
        have h10 : 0 ≤ ∑ ij ∈ offDiag, f ij^2 := by
          apply Finset.sum_nonneg
          intro _ _
          exact sq_nonneg _
        nlinarith
      have h_m_pos : (m : ℝ) > 0 := by exact_mod_cast hm
      have h_sum_sq_lower : ∑ ij ∈ offDiag, f ij^2 ≥ (p : ℝ)^2 / (m : ℝ)^2 := by
        by_cases hc : offDiag.card = 0
        · have hp0 : (p : ℝ) = 0 := by
            have h' : offDiag = ∅ := by simpa using hc
            have h_total : totalIntersection A = 0 := by
              unfold totalIntersection
              have h_goal : ∑ ij ∈ Finset.univ.offDiag, pairIntersection A ij.1 ij.2 = 0 := by
                have h_eq : Finset.univ.offDiag = (∅ : Finset (Fin m × Fin m)) := by
                  exact_mod_cast h'
                rw [h_eq]
                <;> simp
              exact h_goal
            have h_p0 : p = 0 := by
              rw [hp, h_total] <;> rfl
            exact_mod_cast h_p0
          rw [hp0]
          simpa using Finset.sum_nonneg (fun ij _ => sq_nonneg (f ij))
        · have hc' : 0 < (offDiag.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hc)
          have h_ne : (offDiag.card : ℝ) ≠ 0 := by linarith
          have h : (p : ℝ)^2 ≤ (offDiag.card : ℝ) * ∑ ij ∈ offDiag, f ij^2 := h_cs
          calc
            ∑ ij ∈ offDiag, f ij^2
              ≥ (p : ℝ)^2 / (offDiag.card : ℝ) := by
                have h_div : (p : ℝ)^2 / (offDiag.card : ℝ) ≤ ∑ ij ∈ offDiag, f ij^2 := by
                  calc
                    (p : ℝ)^2 / (offDiag.card : ℝ)
                      ≤ ((offDiag.card : ℝ) * ∑ ij ∈ offDiag, f ij^2) / (offDiag.card : ℝ) := by gcongr
                    _ = ∑ ij ∈ offDiag, f ij^2 := by
                      field_simp [h_ne] <;> ring
                exact h_div
            _ ≥ (p : ℝ)^2 / (m : ℝ)^2 := by
              have h11 : (offDiag.card : ℝ) ≤ (m : ℝ)^2 := by exact_mod_cast h_card
              have h12 : 0 ≤ (p : ℝ)^2 := by positivity
              have h13 : 0 < (m : ℝ)^2 := by positivity
              exact div_le_div_of_nonneg_left h12 hc' h11
      have hV_pos : 0 < V := by
        rw [hV_def]
        apply Finset.sum_pos
        · intro l hl
          have h : 0 < w l := hw_pos l hl
          positivity
        · exact Finset.nonempty_Icc.mpr (by omega)
      have h_combined : - (m : ℝ) * (d : ℝ)^2 * U ≤
          (p : ℝ) * W - (p : ℝ)^2 / (12 * (m : ℝ)^2 * V) := by
        calc
          - (m : ℝ) * (d : ℝ)^2 * U
            ≤ ∑ ij ∈ offDiag, S A k w alphabet ij.1 ij.2 := h_lower
          _ ≤ W * (p : ℝ) - (1 / (12 * V)) * ∑ ij ∈ offDiag, (pairIntersection A ij.1 ij.2 : ℝ)^2 := h_sum_upper
          _ ≤ W * (p : ℝ) - (1 / (12 * V)) * ((p : ℝ)^2 / (m : ℝ)^2) := by
              have h_posV : 0 < 1 / (12 * V) := by positivity
              have h : (1 / (12 * V)) * ∑ ij ∈ offDiag, f ij^2 ≥ (1 / (12 * V)) * ((p : ℝ)^2 / (m : ℝ)^2) := by
                gcongr
                <;> exact h_sum_sq_lower
              linarith
          _ = (p : ℝ) * W - (p : ℝ)^2 / (12 * (m : ℝ)^2 * V) := by
              field_simp [hV_pos.ne'] <;> ring
      exact TheoremWiring.final_bound_with_combined
        (hm := hm) (hn := hn_pos)
        (hcard := hcard) (hnodup := hnodup) (hlen := hlen) (halph := halph)
        (k := k) (hk := hk) (p := p) (hp := hp)
        (W := W) (V := V) (U := U)
        (hW_def := hW_def) (hV_def := hV_def) (hU_def := hU_def)
        (h_combined := h_combined)

/-! ### Main theorem -/

/-- The equal-length Marcus-Tardos bound. -/
theorem equal_length_sequence_bound : EqualLengthSequenceBoundStatement :=
  fun α _ => ⟨64, by norm_num, fun m d n hm alphabet hcard A hnodup' halph' hir =>
    main_proof_core α m d n hm alphabet hcard A hnodup' halph' hir⟩

end MarcusTardos.MainProof
