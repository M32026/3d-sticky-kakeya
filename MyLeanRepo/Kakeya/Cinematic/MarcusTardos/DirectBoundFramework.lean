import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.ConcreteBlockSum
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.OrderFunction
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.SingularPairs
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.LeaderPairs
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# Direct S bound framework

Assembles the direct bound on S^{ij} using the telescoping approach.
Takes good-contribution and singular-pair-count as assumptions.
-/

namespace MarcusTardos.DirectBoundFramework

open BigOperators Finset
open scoped Classical

variable {α : Type*} [DecidableEq α]

/-! ### Definitions -/

/-- Intersection size of two blocks. -/
noncomputable def blockPairR (A B : List α) (s t : List Bool) : ℕ :=
  ((block A s).toFinset ∩ (block B t).toFinset).card

/-- Sum of orderFun2 over common elements of two blocks. -/
noncomputable def blockPairC (A B : List α) (s t : List Bool) : ℤ :=
  ∑ p ∈ ((block A s).toFinset ∩ (block B t).toFinset).offDiag,
    orderFun2 (block A s) (block B t) p.1 p.2

/-- All block pairs at level l. -/
def allPairs (l : ℕ) : Finset (List Bool × List Bool) :=
  binaryStrings l ×ˢ binaryStrings l

/-- A block pair is IR. -/
def isPairIR (A B : List α) (st : List Bool × List Bool) : Prop :=
  IsIntersectionReverse (block A st.1) (block B st.2)

/-- Set of singular (active, non-IR) block pairs at level l. -/
noncomputable def singularPairs (A B : List α) (l : ℕ) : Finset (List Bool × List Bool) :=
  (allPairs l).filter (fun st =>
    blockPairR A B st.1 st.2 > 0 ∧ ¬isPairIR A B st)

/-- Total intersection in singular pairs at level l. -/
noncomputable def singularIntersection (A B : List α) (l : ℕ) : ℝ :=
  ∑ st ∈ singularPairs A B l, (blockPairR A B st.1 st.2 : ℝ)

/-- Total good contribution at level l: ∑ (r - c). -/
noncomputable def goodContribution (A B : List α) (l : ℕ) : ℝ :=
  ∑ st ∈ allPairs l,
    ((blockPairR A B st.1 st.2 : ℝ) - (blockPairC A B st.1 st.2 : ℝ))

/-- Assumption: every block pair has r - c ≥ 0. -/
def GoodContributionHyp (A B : List α) : Prop :=
  ∀ (s t : List Bool), (blockPairR A B s t : ℤ) - blockPairC A B s t ≥ 0

/-- Assumption: at most M singular pairs per level. -/
def SingularCountHyp (A B : List α) (M : ℕ) : Prop :=
  ∀ l, 0 < l → (singularPairs A B l).card ≤ M

/-! ### Level sum decomposition -/

/-- Restrict double sum to intersection offDiag. -/
private lemma sum_restrict_to_intersection {Bs Bt : List α}
    (hBs : Bs.Nodup) (hBt : Bt.Nodup)
    (alphabet : Finset α) (halphBs : ∀ x ∈ Bs, x ∈ alphabet)
    (halphBt : ∀ x ∈ Bt, x ∈ alphabet) :
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
      (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) =
    ∑ p ∈ (Bs.toFinset ∩ Bt.toFinset).offDiag, (orderFun2 Bs Bt p.1 p.2 : ℝ) := by
  let I := Bs.toFinset ∩ Bt.toFinset
  have hI_sub : I ⊆ alphabet := by
    intro x hx
    have h5 : x ∈ Bs := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hx).1
    exact halphBs x h5
  have h_zero : ∀ (a b : α), a ∉ I ∨ b ∉ I →
      (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) = 0 := by
    intro a b h
    rcases h with (h | h)
    · have h_i : a ∉ I := h
      have h' : a ∉ Bs ∨ a ∉ Bt := by
        simp only [I, Finset.mem_inter, List.mem_toFinset] at h_i ⊢ <;> tauto
      rcases h' with (h' | h')
      · have h1 : orderFun Bs a b = 0 := by rw [orderFun_eq_zero_iff] <;> tauto
        rw [h1] <;> norm_num
      · have h2 : orderFun Bt a b = 0 := by rw [orderFun_eq_zero_iff] <;> tauto
        rw [h2] <;> norm_num
    · have h_i : b ∉ I := h
      have h' : b ∉ Bs ∨ b ∉ Bt := by
        simp only [I, Finset.mem_inter, List.mem_toFinset] at h_i ⊢ <;> tauto
      rcases h' with (h' | h')
      · have h1 : orderFun Bs a b = 0 := by rw [orderFun_eq_zero_iff] <;> tauto
        rw [h1] <;> norm_num
      · have h2 : orderFun Bt a b = 0 := by rw [orderFun_eq_zero_iff] <;> tauto
        rw [h2] <;> norm_num
  let P : Finset (α × α) := alphabet.offDiag
  have h1 : I.offDiag ⊆ P := by
    intro p hp
    have h6 : p.1 ∈ I := (Finset.mem_offDiag.mp hp).1
    have h7 : p.2 ∈ I := (Finset.mem_offDiag.mp hp).2.1
    have h8 : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    exact Finset.mem_offDiag.mpr ⟨hI_sub h6, hI_sub h7, h8⟩
  have h_main : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) =
      ∑ p ∈ P, (orderFun Bs p.1 p.2 : ℝ) * (orderFun Bt p.1 p.2 : ℝ) := by
    have h_off : P = (alphabet ×ˢ alphabet).filter (fun p : α × α => p.1 ≠ p.2) := by
      ext ⟨a, b⟩
      simp [P, Finset.mem_offDiag] <;> tauto
    rw [h_off]
    have h : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) =
        ∑ p ∈ (alphabet ×ˢ alphabet).filter (fun p : α × α => p.1 ≠ p.2),
          (orderFun Bs p.1 p.2 : ℝ) * (orderFun Bt p.1 p.2 : ℝ) := by
      have h_step1 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) =
          ∑ a ∈ alphabet, ∑ b ∈ alphabet, (if a ≠ b then (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        have h21 : alphabet.filter (fun b => a ≠ b) = alphabet.erase a := by
          ext x
          simp [Finset.mem_erase] <;> tauto
        have h_eq : ∑ b ∈ alphabet, (if a ≠ b then (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) else 0) =
            ∑ b ∈ alphabet.filter (fun b => a ≠ b), (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) := by
          rw [Finset.sum_ite] <;> simp
        rw [h_eq, h21]
      rw [h_step1]
      have h_step2 : ∑ a ∈ alphabet, ∑ b ∈ alphabet, (if a ≠ b then (orderFun Bs a b : ℝ) * (orderFun Bt a b : ℝ) else 0) =
          ∑ p ∈ alphabet ×ˢ alphabet, (if p.1 ≠ p.2 then (orderFun Bs p.1 p.2 : ℝ) * (orderFun Bt p.1 p.2 : ℝ) else 0) := by
        rw [Finset.sum_product] <;> rfl
      rw [h_step2, Finset.sum_filter] <;> rfl
    exact h
  rw [h_main]
  have h2 : ∑ p ∈ P, (orderFun Bs p.1 p.2 : ℝ) * (orderFun Bt p.1 p.2 : ℝ) =
      ∑ p ∈ I.offDiag, (orderFun Bs p.1 p.2 : ℝ) * (orderFun Bt p.1 p.2 : ℝ) := by
    rw [Finset.sum_subset h1]
    intro p hp hnp
    have h9 : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have h10 : p.1 ∉ I ∨ p.2 ∉ I := by
      by_contra h11
      push Not at h11
      exact hnp (Finset.mem_offDiag.mpr ⟨h11.1, h11.2, h9⟩)
    exact h_zero p.1 p.2 h10
  rw [h2]
  apply Finset.sum_congr rfl
  intro p _
  simp [orderFun2] <;> rfl

/-- Level-l inner product equals sum of blockPairC. -/
lemma level_sum_decomposition {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (l : ℕ) (alphabet : Finset α)
    (halphA : ∀ x ∈ A, x ∈ alphabet) (halphB : ∀ x ∈ B, x ∈ alphabet) :
    ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
      (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ) =
    ∑ st ∈ allPairs l, (blockPairC A B st.1 st.2 : ℝ) := by
  have h1 : ∀ (a : α) (b : α),
      (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ) =
      ∑ st ∈ allPairs l,
        (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) := by
    intro a b
    have hGA : (ConcreteBlockSum.G A l a b : ℝ) =
        ∑ s ∈ binaryStrings l, (orderFun (block A s) a b : ℝ) := by rfl
    have hGB : (ConcreteBlockSum.G B l a b : ℝ) =
        ∑ t ∈ binaryStrings l, (orderFun (block B t) a b : ℝ) := by rfl
    calc
      (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ)
        = (∑ s ∈ binaryStrings l, (orderFun (block A s) a b : ℝ)) *
          (∑ t ∈ binaryStrings l, (orderFun (block B t) a b : ℝ)) := by rw [hGA, hGB]
      _ = ∑ s ∈ binaryStrings l, ∑ t ∈ binaryStrings l,
            (orderFun (block A s) a b : ℝ) * (orderFun (block B t) a b : ℝ) := by
        rw [Finset.sum_mul_sum]
      _ = ∑ st ∈ binaryStrings l ×ˢ binaryStrings l,
            (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) := by
        rw [Finset.sum_product] <;> rfl
      _ = ∑ st ∈ allPairs l, (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) := by
        rfl
  have h_step1 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ) =
      ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, ∑ st ∈ allPairs l,
        (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact h1 a b
  rw [h_step1]
  have h_step2 : ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a, ∑ st ∈ allPairs l,
        (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) =
      ∑ st ∈ allPairs l, ∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (orderFun (block A st.1) a b : ℝ) * (orderFun (block B st.2) a b : ℝ) := by
    have h_comm : ∀ (X : Finset α) (Y : α → Finset α) (Z : Finset (List Bool × List Bool))
        (h : α → α → (List Bool × List Bool) → ℝ),
        ∑ a ∈ X, ∑ b ∈ Y a, ∑ z ∈ Z, h a b z =
        ∑ z ∈ Z, ∑ a ∈ X, ∑ b ∈ Y a, h a b z := by
      intro X Y Z h
      calc
        ∑ a ∈ X, ∑ b ∈ Y a, ∑ z ∈ Z, h a b z
          = ∑ a ∈ X, ∑ z ∈ Z, ∑ b ∈ Y a, h a b z := by
            apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
        _ = ∑ z ∈ Z, ∑ a ∈ X, ∑ b ∈ Y a, h a b z := by rw [Finset.sum_comm]
    exact h_comm alphabet (fun a => alphabet.erase a) (allPairs l) _
  rw [h_step2]
  apply Finset.sum_congr rfl
  intro st _
  have hBs_nodup : (block A st.1).Nodup := block_nodup hA st.1
  have hBt_nodup : (block B st.2).Nodup := block_nodup hB st.2
  have halphBs : ∀ x ∈ block A st.1, x ∈ alphabet := by
    intro x hx
    exact halphA x (block_sublist A st.1 |>.subset hx)
  have halphBt : ∀ x ∈ block B st.2, x ∈ alphabet := by
    intro x hx
    exact halphB x (block_sublist B st.2 |>.subset hx)
  have h_res := sum_restrict_to_intersection hBs_nodup hBt_nodup alphabet halphBs halphBt
  simpa [blockPairC] using h_res

/-- For an IR block pair, r - c = r². -/
lemma ir_pair_r_minus_c {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    {s t : List Bool} (hIR : IsIntersectionReverse (block A s) (block B t)) :
    (blockPairR A B s t : ℤ) - blockPairC A B s t = (blockPairR A B s t : ℤ)^2 := by
  let I := (block A s).toFinset ∩ (block B t).toFinset
  have h1 : (block A s).Nodup := block_nodup hA s
  have h2 : (block B t).Nodup := block_nodup hB t
  have h_main : ∑ p ∈ I.offDiag, orderFun2 (block A s) (block B t) p.1 p.2 =
      (I.card : ℤ) - (I.card : ℤ)^2 :=
    sum_orderFun2_of_intersectionReverse h1 h2 hIR
  have hr : (blockPairR A B s t : ℤ) = (I.card : ℤ) := by
    simp [blockPairR] <;> norm_cast
  have hc : blockPairC A B s t = ∑ p ∈ I.offDiag, orderFun2 (block A s) (block B t) p.1 p.2 := by
    simp [blockPairC] <;> rfl
  rw [hc, h_main, hr] <;> ring

/-! ### Block child properties -/

/-- Left child block equals leftHalf of parent. -/
lemma block_child_left (A : List α) (s : List Bool) :
    block A (s ++ [false]) = leftHalf (block A s) := by
  induction s generalizing A with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | false => simpa [block] using ih (leftHalf A)
    | true => simpa [block] using ih (rightHalf A)

/-- Right child block equals rightHalf of parent. -/
lemma block_child_right (A : List α) (s : List Bool) :
    block A (s ++ [true]) = rightHalf (block A s) := by
  induction s generalizing A with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | false => simpa [block] using ih (leftHalf A)
    | true => simpa [block] using ih (rightHalf A)

/-- Children of IR pairs are IR. -/
lemma ir_children_are_ir {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    {s t : List Bool} (hIR : isPairIR A B (s, t))
    (b1 b2 : Bool) :
    isPairIR A B (s ++ [b1], t ++ [b2]) := by
  have hsub1 : (block A (s ++ [b1])).Sublist (block A s) := by
    cases b1 with
    | false => rw [block_child_left A s]; exact List.take_sublist _ _
    | true => rw [block_child_right A s]; exact List.drop_sublist _ _
  have hsub2 : (block B (t ++ [b2])).Sublist (block B t) := by
    cases b2 with
    | false => rw [block_child_left B t]; exact List.take_sublist _ _
    | true => rw [block_child_right B t]; exact List.drop_sublist _ _
  have hBs : (block A s).Nodup := block_nodup hA s
  have hBt : (block B t).Nodup := block_nodup hB t
  exact hIR.sublist hBs hBt hsub1 hsub2

/-- If the level-0 block pair is IR, then all block pairs at all levels are IR. -/
lemma all_pairs_ir_of_level0_ir {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (hIR0 : isPairIR A B ([], [])) :
    ∀ (l : ℕ) (st : List Bool × List Bool), st ∈ allPairs l → isPairIR A B st := by
  intro l
  induction l with
  | zero =>
    intro st hst
    have h3 : st = ([], []) := by
      have h4 : st ∈ ({([], [])} : Finset (List Bool × List Bool)) := by
        simpa [allPairs, binaryStrings] using hst
      simpa using h4
    rw [h3]
    exact hIR0
  | succ l ih =>
    intro st hst
    have hlen1 : st.1.length = l + 1 := binaryStrings_mem.mp (Finset.mem_product.mp hst).1
    have hlen2 : st.2.length = l + 1 := binaryStrings_mem.mp (Finset.mem_product.mp hst).2
    have hne1 : st.1 ≠ [] := by
      intro h; rw [h] at hlen1; simp at hlen1 <;> omega
    have hne2 : st.2 ≠ [] := by
      intro h; rw [h] at hlen2; simp at hlen2 <;> omega
    let b1 := st.1.getLast hne1
    let b2 := st.2.getLast hne2
    have h5 : st.1.dropLast.length = l := by
      rw [List.length_dropLast, hlen1] <;> omega
    have h6 : st.2.dropLast.length = l := by
      rw [List.length_dropLast, hlen2] <;> omega
    have h_par : (st.1.dropLast, st.2.dropLast) ∈ allPairs l := by
      simp [allPairs, binaryStrings_mem, h5, h6]
    have hIR_par := ih (st.1.dropLast, st.2.dropLast) h_par
    have h71 : st.1.dropLast ++ [b1] = st.1 := List.dropLast_append_getLast hne1
    have h72 : st.2.dropLast ++ [b2] = st.2 := List.dropLast_append_getLast hne2
    have h7 : st = (st.1.dropLast ++ [b1], st.2.dropLast ++ [b2]) := by
      exact Prod.ext h71.symm h72.symm
    rw [h7]
    exact ir_children_are_ir hA hB hIR_par b1 b2

/-- At level k where 2^k ≥ d, all block pairs are IR. -/
lemma all_pairs_ir_at_level_k {d : ℕ} {A B : List α}
    (hA : A.Nodup) (hB : B.Nodup)
    (hlenA : A.length = d) (hlenB : B.length = d)
    {k : ℕ} (hk : 2^k ≥ d) {s t : List Bool}
    (hs : s.length = k) (ht : t.length = k) :
    isPairIR A B (s, t) :=
  SingularPairs.level_k_all_ir hA hB hlenA hlenB hk hs ht

/-- Child block is a sublist of parent block. -/
lemma block_child_sublist_parent (A : List α) {s : List Bool} (hs : s ≠ []) :
    (block A s).Sublist (block A s.dropLast) := by
  induction s generalizing A with
  | nil => contradiction
  | cons b s' ih =>
    by_cases h : s' = []
    · subst h
      simp [List.dropLast, block]
      cases b with
      | false => exact List.take_sublist _ _
      | true => exact List.drop_sublist _ _
    · let C := if b then rightHalf A else leftHalf A
      have h_ih' : (block C s').Sublist (block C s'.dropLast) := ih C h
      have h_eq1 : block A (b :: s') = block C s' := by
        cases b <;> simp [block, C] <;> rfl
      have h_eq2 : block A ((b :: s').dropLast) = block C s'.dropLast := by
        have hdl : (b :: s').dropLast = b :: s'.dropLast := by
          simp [List.dropLast]
        rw [hdl]
        cases b <;> simp [block, C] <;> rfl
      rw [h_eq1, h_eq2]
      exact h_ih'

/-! ### Block intersection disjointness and partition -/

/-- Intersection sets of distinct block pairs at same level are disjoint. -/
lemma blockPair_intersections_disjoint {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    {l : ℕ} {st1 st2 : List Bool × List Bool}
    (h1 : st1 ∈ allPairs l) (h2 : st2 ∈ allPairs l) (hne : st1 ≠ st2) :
    Disjoint ((block A st1.1).toFinset ∩ (block B st1.2).toFinset)
        ((block A st2.1).toFinset ∩ (block B st2.2).toFinset) := by
  have hlen11 : st1.1.length = l := binaryStrings_mem.mp (Finset.mem_product.mp h1).1
  have hlen21 : st2.1.length = l := binaryStrings_mem.mp (Finset.mem_product.mp h2).1
  have hlen12 : st1.2.length = l := binaryStrings_mem.mp (Finset.mem_product.mp h1).2
  have hlen22 : st2.2.length = l := binaryStrings_mem.mp (Finset.mem_product.mp h2).2
  have h_multiset_to_finset : ∀ {l1 l2 : List α},
      Disjoint (l1 : Multiset α) (l2 : Multiset α) → Disjoint l1.toFinset l2.toFinset := by
    intro l1 l2 h
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1' : x ∈ (l1 : Multiset α) := by
      simpa [Multiset.mem_coe] using hx1
    have h2' : x ∈ (l2 : Multiset α) := by
      simpa [Multiset.mem_coe] using hx2
    exact Multiset.disjoint_left.mp h h1' h2'
  by_cases h : st1.1 = st2.1
  · have h' : st1.2 ≠ st2.2 := by
      intro h''
      apply hne
      exact Prod.ext h h''
    have hdisj : Disjoint (block B st1.2 : Multiset α) (block B st2.2) :=
      block_disjoint hB (by rw [hlen12, hlen22]) h'
    have hfin : Disjoint (block B st1.2).toFinset (block B st2.2).toFinset :=
      h_multiset_to_finset hdisj
    rw [Finset.disjoint_left] at hfin ⊢
    intro x hx1 hx2
    have h1 : x ∈ (block B st1.2).toFinset := (Finset.mem_inter.mp hx1).2
    have h2 : x ∈ (block B st2.2).toFinset := (Finset.mem_inter.mp hx2).2
    exact hfin h1 h2
  · have hdisj : Disjoint (block A st1.1 : Multiset α) (block A st2.1) :=
      block_disjoint hA (by rw [hlen11, hlen21]) h
    have hfin : Disjoint (block A st1.1).toFinset (block A st2.1).toFinset :=
      h_multiset_to_finset hdisj
    rw [Finset.disjoint_left] at hfin ⊢
    intro x hx1 hx2
    have h1 : x ∈ (block A st1.1).toFinset := (Finset.mem_inter.mp hx1).1
    have h2 : x ∈ (block A st2.1).toFinset := (Finset.mem_inter.mp hx2).1
    exact hfin h1 h2

/-- Sum of blockPairR over all pairs equals total intersection size. -/
lemma sum_blockPairR_eq {A B : List α} (hA : A.Nodup) (hB : B.Nodup) (l : ℕ) :
    ∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ) =
    ((A.toFinset ∩ B.toFinset).card : ℝ) := by
  let I : List Bool × List Bool → Finset α := fun st =>
    (block A st.1).toFinset ∩ (block B st.2).toFinset
  have h_disj : ∀ st1 ∈ allPairs l, ∀ st2 ∈ allPairs l, st1 ≠ st2 → Disjoint (I st1) (I st2) :=
    fun st1 hst1 st2 hst2 hne => blockPair_intersections_disjoint hA hB hst1 hst2 hne
  have h_union : (allPairs l).biUnion I = A.toFinset ∩ B.toFinset := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, List.mem_toFinset]
    constructor
    · rintro ⟨st, hst, hx⟩
      have h1 : x ∈ (block A st.1).toFinset := (Finset.mem_inter.mp hx).1
      have h2 : x ∈ (block B st.2).toFinset := (Finset.mem_inter.mp hx).2
      have h1' : x ∈ block A st.1 := by simpa [List.mem_toFinset] using h1
      have h2' : x ∈ block B st.2 := by simpa [List.mem_toFinset] using h2
      have h3 : x ∈ A := (block_sublist A st.1).subset h1'
      have h4 : x ∈ B := (block_sublist B st.2).subset h2'
      exact ⟨h3, h4⟩
    · rintro ⟨hxA, hxB⟩
      rcases block_exists hxA l with ⟨s, hsl, hxs⟩
      rcases block_exists hxB l with ⟨t, htl, hxt⟩
      have hst : (s, t) ∈ allPairs l := by
        simp [allPairs, binaryStrings_mem, hsl, htl]
      refine' ⟨(s, t), hst, _⟩
      have hxs' : x ∈ (block A s).toFinset := by simpa [List.mem_toFinset] using hxs
      have hxt' : x ∈ (block B t).toFinset := by simpa [List.mem_toFinset] using hxt
      exact Finset.mem_inter.mpr ⟨hxs', hxt'⟩
  have h_sum_nat : ∑ st ∈ allPairs l, (I st).card = ((allPairs l).biUnion I).card := by
    rw [Finset.card_biUnion h_disj]
  have h_sum : ∑ st ∈ allPairs l, ((I st).card : ℝ) = (((allPairs l).biUnion I).card : ℝ) := by
    exact_mod_cast h_sum_nat
  have h_main : ∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ) =
      ∑ st ∈ allPairs l, ((I st).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro st _
    simp [blockPairR, I] <;> norm_cast
  rw [h_main, h_sum, h_union] <;> norm_cast

/-! ### singularIntersection monotonicity -/

/-- singularIntersection is non-increasing: s_l ≤ s_{l-1}. -/
lemma singularIntersection_decr {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    {l : ℕ} (hl : 0 < l) :
    singularIntersection A B l ≤ singularIntersection A B (l - 1) := by
  let P_l := singularPairs A B l
  let P_prev := singularPairs A B (l - 1)
  let I : List Bool × List Bool → Finset α := fun st =>
    (block A st.1).toFinset ∩ (block B st.2).toFinset
  let parent : List Bool × List Bool → List Bool × List Bool :=
    fun st => (st.1.dropLast, st.2.dropLast)
  have hP_l_sub : P_l ⊆ allPairs l := Finset.filter_subset _ _
  have hP_prev_sub : P_prev ⊆ allPairs (l - 1) := Finset.filter_subset _ _
  have h_disj_l : ∀ st1 ∈ P_l, ∀ st2 ∈ P_l, st1 ≠ st2 → Disjoint (I st1) (I st2) := by
    intro st1 hst1 st2 hst2 hne
    exact blockPair_intersections_disjoint hA hB (hP_l_sub hst1) (hP_l_sub hst2) hne
  have h_disj_prev : ∀ pt1 ∈ P_prev, ∀ pt2 ∈ P_prev, pt1 ≠ pt2 → Disjoint (I pt1) (I pt2) := by
    intro pt1 hpt1 pt2 hpt2 hne
    exact blockPair_intersections_disjoint hA hB (hP_prev_sub hpt1) (hP_prev_sub hpt2) hne
  have h_sublist_to_finset : ∀ {l1 l2 : List α}, l1.Sublist l2 → l1.toFinset ⊆ l2.toFinset := by
    intro l1 l2 h x hx
    have hx' : x ∈ l1 := by simpa [List.mem_toFinset] using hx
    have hx'' : x ∈ l2 := h.subset hx'
    simpa [List.mem_toFinset] using hx''
  have h_parent_mem : ∀ st ∈ P_l, parent st ∈ P_prev := by
    intro st hst
    have hst_all : st ∈ allPairs l := hP_l_sub hst
    have hlen1 : st.1.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).1
    have hlen2 : st.2.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).2
    have hne1 : st.1 ≠ [] := by
      intro h; rw [h] at hlen1; simp at hlen1 <;> omega
    have hne2 : st.2 ≠ [] := by
      intro h; rw [h] at hlen2; simp at hlen2 <;> omega
    have hR_pos : blockPairR A B st.1 st.2 > 0 := (Finset.mem_filter.mp hst).2.1
    have hnotIR : ¬isPairIR A B st := (Finset.mem_filter.mp hst).2.2
    have hpar_all : parent st ∈ allPairs (l - 1) := by
      have h1 : (st.1.dropLast).length = l - 1 := by
        rw [List.length_dropLast] <;> omega
      have h2 : (st.2.dropLast).length = l - 1 := by
        rw [List.length_dropLast] <;> omega
      simp [parent, allPairs, binaryStrings_mem, h1, h2]
    have hsub1 : (block A st.1).Sublist (block A (parent st).1) :=
      block_child_sublist_parent (A := A) (s := st.1) hne1
    have hsub2 : (block B st.2).Sublist (block B (parent st).2) :=
      block_child_sublist_parent (A := B) (s := st.2) hne2
    have hI_sub : I st ⊆ I (parent st) :=
      Finset.inter_subset_inter (h_sublist_to_finset hsub1) (h_sublist_to_finset hsub2)
    have hR_par_pos : blockPairR A B (parent st).1 (parent st).2 > 0 := by
      have h_nonempty : (I st).Nonempty := Finset.card_pos.mp hR_pos
      have h : (I (parent st)).Nonempty := h_nonempty.mono hI_sub
      exact Finset.card_pos.mpr h
    have hnotIR_par : ¬isPairIR A B (parent st) := by
      intro hIR
      let b1 := st.1.getLast hne1
      let b2 := st.2.getLast hne2
      have h1 : st.1.dropLast ++ [b1] = st.1 := List.dropLast_append_getLast hne1
      have h2 : st.2.dropLast ++ [b2] = st.2 := List.dropLast_append_getLast hne2
      have h_st_eq : st = ((parent st).1 ++ [b1], (parent st).2 ++ [b2]) := by
        exact Prod.ext h1.symm h2.symm
      have h_goal : isPairIR A B ((parent st).1 ++ [b1], (parent st).2 ++ [b2]) :=
        ir_children_are_ir hA hB hIR b1 b2
      have h_final : isPairIR A B st := by
        rw [h_st_eq]
        exact h_goal
      exact hnotIR h_final
    exact Finset.mem_filter.mpr ⟨hpar_all, hR_par_pos, hnotIR_par⟩
  have hI_sub : ∀ st ∈ P_l, I st ⊆ I (parent st) := by
    intro st hst
    have hst_all : st ∈ allPairs l := hP_l_sub hst
    have hlen1 : st.1.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).1
    have hlen2 : st.2.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).2
    have hne1 : st.1 ≠ [] := by
      intro h; rw [h] at hlen1; simp at hlen1 <;> omega
    have hne2 : st.2 ≠ [] := by
      intro h; rw [h] at hlen2; simp at hlen2 <;> omega
    have hsub1 : (block A st.1).Sublist (block A (parent st).1) :=
      block_child_sublist_parent (A := A) (s := st.1) hne1
    have hsub2 : (block B st.2).Sublist (block B (parent st).2) :=
      block_child_sublist_parent (A := B) (s := st.2) hne2
    exact Finset.inter_subset_inter (h_sublist_to_finset hsub1) (h_sublist_to_finset hsub2)
  have h_union_sub : P_l.biUnion I ⊆ P_prev.biUnion I := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨st, hst, hxI⟩
    have hpt : parent st ∈ P_prev := h_parent_mem st hst
    have h : x ∈ I (parent st) := hI_sub st hst hxI
    exact Finset.mem_biUnion.mpr ⟨parent st, hpt, h⟩
  have h_sum_l_nat : ∑ st ∈ P_l, (I st).card = (P_l.biUnion I).card := by
    rw [Finset.card_biUnion h_disj_l]
  have h_sum_prev_nat : ∑ pt ∈ P_prev, (I pt).card = (P_prev.biUnion I).card := by
    rw [Finset.card_biUnion h_disj_prev]
  have h_main : ∑ st ∈ P_l, (blockPairR A B st.1 st.2 : ℝ) = ∑ st ∈ P_l, ((I st).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro st _
    simp [blockPairR, I] <;> norm_cast
  have h_main2 : ∑ pt ∈ P_prev, (blockPairR A B pt.1 pt.2 : ℝ) = ∑ pt ∈ P_prev, ((I pt).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro pt _
    simp [blockPairR, I] <;> norm_cast
  have h_sum_l_cast : ∑ st ∈ P_l, ((I st).card : ℝ) = ((P_l.biUnion I).card : ℝ) := by
    simpa [Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h_sum_l_nat
  have h_sum_prev_cast : ∑ pt ∈ P_prev, ((I pt).card : ℝ) = ((P_prev.biUnion I).card : ℝ) := by
    simpa [Nat.cast_sum] using congr_arg (fun x : ℕ => (x : ℝ)) h_sum_prev_nat
  have h_union_cast : ((P_l.biUnion I).card : ℝ) ≤ ((P_prev.biUnion I).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_union_sub
  calc
    ∑ st ∈ P_l, (blockPairR A B st.1 st.2 : ℝ)
      = ∑ st ∈ P_l, ((I st).card : ℝ) := h_main
    _ = ((P_l.biUnion I).card : ℝ) := h_sum_l_cast
    _ ≤ ((P_prev.biUnion I).card : ℝ) := h_union_cast
    _ = ∑ pt ∈ P_prev, ((I pt).card : ℝ) := h_sum_prev_cast.symm
    _ = ∑ pt ∈ P_prev, (blockPairR A B pt.1 pt.2 : ℝ) := h_main2.symm

/-! ### Children partition and good contribution bound -/

/-- The four children of a block pair. -/
def childrenOf (st : List Bool × List Bool) : Finset (List Bool × List Bool) :=
  {(st.1 ++ [false], st.2 ++ [false]),
   (st.1 ++ [false], st.2 ++ [true]),
   (st.1 ++ [true], st.2 ++ [false]),
   (st.1 ++ [true], st.2 ++ [true])}

/-- The four children are distinct. -/
lemma childrenOf_card (st : List Bool × List Bool) : (childrenOf st).card = 4 := by
  simp [childrenOf] <;> decide

/-- Children of distinct parents are disjoint. -/
lemma childrenOf_disjoint {st1 st2 : List Bool × List Bool} (hne : st1 ≠ st2) :
    Disjoint (childrenOf st1) (childrenOf st2) := by
  rw [Finset.disjoint_left]
  intro c hc1 hc2
  have h1 : c.1.dropLast = st1.1 ∧ c.2.dropLast = st1.2 := by
    simp only [childrenOf, Finset.mem_insert, Finset.mem_singleton] at hc1
    rcases hc1 with (rfl | rfl | rfl | rfl) <;> simp [List.dropLast_append] <;> tauto
  have h2 : c.1.dropLast = st2.1 ∧ c.2.dropLast = st2.2 := by
    simp only [childrenOf, Finset.mem_insert, Finset.mem_singleton] at hc2
    rcases hc2 with (rfl | rfl | rfl | rfl) <;> simp [List.dropLast_append] <;> tauto
  have h3 : st1.1 = st2.1 := h1.1.symm.trans h2.1
  have h4 : st1.2 = st2.2 := h1.2.symm.trans h2.2
  have h5 : st1 = st2 := Prod.ext h3 h4
  exact hne h5

/-- For a nodup list, leftHalf and rightHalf have disjoint finsets. -/
lemma halves_finset_disjoint {X : List α} (hX : X.Nodup) :
    Disjoint (leftHalf X).toFinset (rightHalf X).toFinset := by
  have h : (leftHalf X ++ rightHalf X).Nodup := by
    rw [left_append_right X] <;> exact hX
  have h' : (leftHalf X).Disjoint (rightHalf X) :=
    (List.nodup_append'.mp h).2.2
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have h1 : x ∈ leftHalf X := by simpa [List.mem_toFinset] using hx1
  have h2 : x ∈ rightHalf X := by simpa [List.mem_toFinset] using hx2
  exact h' h1 h2

/-- Sum of children's intersection sizes equals parent's intersection size. -/
lemma children_sum_r {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    {s t : List Bool} :
    ∑ c ∈ childrenOf (s, t), (blockPairR A B c.1 c.2 : ℝ) =
    (blockPairR A B s t : ℝ) := by
  let LX := block A (s ++ [false])
  let RX := block A (s ++ [true])
  let LY := block B (t ++ [false])
  let RY := block B (t ++ [true])
  let I1 := LX.toFinset ∩ LY.toFinset
  let I2 := LX.toFinset ∩ RY.toFinset
  let I3 := RX.toFinset ∩ LY.toFinset
  let I4 := RX.toFinset ∩ RY.toFinset
  let cFF := (s ++ [false], t ++ [false])
  let cFT := (s ++ [false], t ++ [true])
  let cTF := (s ++ [true], t ++ [false])
  let cTT := (s ++ [true], t ++ [true])
  have hX : (block A s).Nodup := block_nodup hA s
  have hY : (block B t).Nodup := block_nodup hB t
  have hLX : LX = leftHalf (block A s) := block_child_left A s
  have hRX : RX = rightHalf (block A s) := block_child_right A s
  have hLY : LY = leftHalf (block B t) := block_child_left B t
  have hRY : RY = rightHalf (block B t) := block_child_right B t
  have h_disjX : Disjoint LX.toFinset RX.toFinset := by
    rw [hLX, hRX]; exact halves_finset_disjoint hX
  have h_disjY : Disjoint LY.toFinset RY.toFinset := by
    rw [hLY, hRY]; exact halves_finset_disjoint hY
  have h_unionX : LX.toFinset ∪ RX.toFinset = (block A s).toFinset := by
    have h_append : LX ++ RX = block A s := block_append A s
    have h2 : (LX ++ RX).toFinset = LX.toFinset ∪ RX.toFinset := by rw [List.toFinset_append]
    have h3 : (LX ++ RX).toFinset = (block A s).toFinset := by rw [h_append]
    rw [←h3, h2]
  have h_unionY : LY.toFinset ∪ RY.toFinset = (block B t).toFinset := by
    have h_append : LY ++ RY = block B t := block_append B t
    have h2 : (LY ++ RY).toFinset = LY.toFinset ∪ RY.toFinset := by rw [List.toFinset_append]
    have h3 : (LY ++ RY).toFinset = (block B t).toFinset := by rw [h_append]
    rw [←h3, h2]
  have h12 : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LY.toFinset := (Finset.mem_inter.mp hx1).2
    have h2 : x ∈ RY.toFinset := (Finset.mem_inter.mp hx2).2
    exact Finset.disjoint_left.mp h_disjY h1 h2
  have h13 : Disjoint I1 I3 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LX.toFinset := (Finset.mem_inter.mp hx1).1
    have h2 : x ∈ RX.toFinset := (Finset.mem_inter.mp hx2).1
    exact Finset.disjoint_left.mp h_disjX h1 h2
  have h14 : Disjoint I1 I4 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LX.toFinset := (Finset.mem_inter.mp hx1).1
    have h2 : x ∈ RX.toFinset := (Finset.mem_inter.mp hx2).1
    exact Finset.disjoint_left.mp h_disjX h1 h2
  have h23 : Disjoint I2 I3 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LX.toFinset := (Finset.mem_inter.mp hx1).1
    have h2 : x ∈ RX.toFinset := (Finset.mem_inter.mp hx2).1
    exact Finset.disjoint_left.mp h_disjX h1 h2
  have h24 : Disjoint I2 I4 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LX.toFinset := (Finset.mem_inter.mp hx1).1
    have h2 : x ∈ RX.toFinset := (Finset.mem_inter.mp hx2).1
    exact Finset.disjoint_left.mp h_disjX h1 h2
  have h34 : Disjoint I3 I4 := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    have h1 : x ∈ LY.toFinset := (Finset.mem_inter.mp hx1).2
    have h2 : x ∈ RY.toFinset := (Finset.mem_inter.mp hx2).2
    exact Finset.disjoint_left.mp h_disjY h1 h2
  have h_disj3 : Disjoint (I1 ∪ I2) I3 := by
    rw [Finset.disjoint_union_left] <;> exact ⟨h13, h23⟩
  have h_disj4 : Disjoint ((I1 ∪ I2) ∪ I3) I4 := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_union_left] <;> exact ⟨h14, h24⟩
    · exact h34
  have h_union : I1 ∪ I2 ∪ I3 ∪ I4 = (block A s).toFinset ∩ (block B t).toFinset := by
    apply Finset.ext
    intro x
    have hA_iff : x ∈ (block A s).toFinset ↔ x ∈ LX.toFinset ∨ x ∈ RX.toFinset := by
      rw [←h_unionX] <;> simp [Finset.mem_union]
    have hB_iff : x ∈ (block B t).toFinset ↔ x ∈ LY.toFinset ∨ x ∈ RY.toFinset := by
      rw [←h_unionY] <;> simp [Finset.mem_union]
    simp only [I1, I2, I3, I4, Finset.mem_union, Finset.mem_inter]
    rw [hA_iff, hB_iff]
    <;> tauto
  have h_card : ((I1 ∪ I2 ∪ I3 ∪ I4).card : ℝ) = (I1.card : ℝ) + (I2.card : ℝ) + (I3.card : ℝ) + (I4.card : ℝ) := by
    rw [Finset.card_union_of_disjoint h_disj4, Finset.card_union_of_disjoint h_disj3, Finset.card_union_of_disjoint h12]
    <;> norm_cast <;> ring
  have h_children : childrenOf (s, t) = {cFF, cFT, cTF, cTT} := by rfl
  have h_sum : ∑ c ∈ childrenOf (s, t), (blockPairR A B c.1 c.2 : ℝ) =
      (I1.card : ℝ) + (I2.card : ℝ) + (I3.card : ℝ) + (I4.card : ℝ) := by
    rw [h_children]
    have h_eq : ∑ c ∈ ({cFF, cFT, cTF, cTT} : Finset _), (blockPairR A B c.1 c.2 : ℝ) =
        (blockPairR A B cFF.1 cFF.2 : ℝ) + (blockPairR A B cFT.1 cFT.2 : ℝ) +
        (blockPairR A B cTF.1 cTF.2 : ℝ) + (blockPairR A B cTT.1 cTT.2 : ℝ) := by
      have h1 : cFF ∉ ({cFT, cTF, cTT} : Finset _) := by simp [cFF, cFT, cTF, cTT] <;> decide
      have h2 : cFT ∉ ({cTF, cTT} : Finset _) := by simp [cFT, cTF, cTT] <;> decide
      have h3 : cTF ∉ ({cTT} : Finset _) := by simp [cTF, cTT] <;> decide
      rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3, Finset.sum_singleton] <;> ring
    rw [h_eq]
    have hI1 : (blockPairR A B cFF.1 cFF.2 : ℝ) = (I1.card : ℝ) := by
      simp [blockPairR, I1, cFF] <;> norm_cast
    have hI2 : (blockPairR A B cFT.1 cFT.2 : ℝ) = (I2.card : ℝ) := by
      simp [blockPairR, I2, cFT] <;> norm_cast
    have hI3 : (blockPairR A B cTF.1 cTF.2 : ℝ) = (I3.card : ℝ) := by
      simp [blockPairR, I3, cTF] <;> norm_cast
    have hI4 : (blockPairR A B cTT.1 cTT.2 : ℝ) = (I4.card : ℝ) := by
      simp [blockPairR, I4, cTT] <;> norm_cast
    rw [hI1, hI2, hI3, hI4] <;> ring
  have h_final : (I1.card : ℝ) + (I2.card : ℝ) + (I3.card : ℝ) + (I4.card : ℝ) = ((block A s).toFinset ∩ (block B t).toFinset).card := by
    calc
      (I1.card : ℝ) + (I2.card : ℝ) + (I3.card : ℝ) + (I4.card : ℝ)
        = ((I1 ∪ I2 ∪ I3 ∪ I4).card : ℝ) := h_card.symm
      _ = (((block A s).toFinset ∩ (block B t).toFinset).card : ℝ) := by rw [h_union]
  rw [h_sum, h_final]
  <;> simp [blockPairR] <;> norm_cast


/-- Good contribution bound via Cauchy-Schwarz on new IR pairs.

Children of singular pairs at level l-1 that become IR at level l
account for the decrease in singular intersection. Cauchy-Schwarz
over at most 4M such pairs gives the bound. -/
lemma good_contribution_bound {A B : List α} (hA : A.Nodup) (hB : B.Nodup)
    (M : ℕ) (hM_pos : 0 < M)
    (h_good : GoodContributionHyp A B) (h_singular : SingularCountHyp A B M)
    {l : ℕ} (hl : 0 < l) :
    goodContribution A B l ≥
    (singularIntersection A B (l - 1) - singularIntersection A B l)^2 / (4 * M : ℝ) := by
  let P := singularPairs A B (l - 1)
  let children_set := P.biUnion childrenOf
  let newIR := children_set.filter (fun st => isPairIR A B st)
  let r : (List Bool × List Bool) → ℝ := fun st => (blockPairR A B st.1 st.2 : ℝ)
  let rest := children_set \ (newIR ∪ singularPairs A B l)
  have h_sublist_to_finset : ∀ {l1 l2 : List α}, l1.Sublist l2 → l1.toFinset ⊆ l2.toFinset := by
    intro l1 l2 h x hx
    have hx' : x ∈ l1 := by simpa [List.mem_toFinset] using hx
    have hx'' : x ∈ l2 := h.subset hx'
    simpa [List.mem_toFinset] using hx''
  have h_children_all : children_set ⊆ allPairs l := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨pt, hpt, hcpt⟩
    have hpt_all : pt ∈ allPairs (l - 1) := (Finset.filter_subset _ _) hpt
    have hpt_len1 : pt.1.length = l - 1 := binaryStrings_mem.mp (Finset.mem_product.mp hpt_all).1
    have hpt_len2 : pt.2.length = l - 1 := binaryStrings_mem.mp (Finset.mem_product.mp hpt_all).2
    simp only [childrenOf, Finset.mem_insert, Finset.mem_singleton] at hcpt
    rcases hcpt with (rfl | rfl | rfl | rfl) <;> simp [allPairs, binaryStrings_mem, hpt_len1, hpt_len2] <;> omega
  have h1 : ∑ c ∈ children_set, r c = singularIntersection A B (l - 1) := by
    have h_sum : ∑ c ∈ children_set, r c = ∑ pt ∈ P, ∑ c ∈ childrenOf pt, r c := by
      rw [Finset.sum_biUnion]
      · intro pt1 _ pt2 _ hne; exact childrenOf_disjoint hne
    rw [h_sum]
    have h2 : ∑ pt ∈ P, ∑ c ∈ childrenOf pt, r c = ∑ pt ∈ P, (blockPairR A B pt.1 pt.2 : ℝ) := by
      apply Finset.sum_congr rfl; intro pt _; exact children_sum_r hA hB
    rw [h2] <;> rfl
  have h2 : singularPairs A B l ⊆ children_set := by
    intro st hst
    have hst_all : st ∈ allPairs l := (Finset.mem_filter.mp hst).1
    have hR_pos : blockPairR A B st.1 st.2 > 0 := (Finset.mem_filter.mp hst).2.1
    have hnotIR : ¬isPairIR A B st := (Finset.mem_filter.mp hst).2.2
    have hlen1 : st.1.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).1
    have hlen2 : st.2.length = l := binaryStrings_mem.mp (Finset.mem_product.mp hst_all).2
    have hne1 : st.1 ≠ [] := by intro h; rw [h] at hlen1; simp at hlen1 <;> omega
    have hne2 : st.2 ≠ [] := by intro h; rw [h] at hlen2; simp at hlen2 <;> omega
    let b1 := st.1.getLast hne1
    let b2 := st.2.getLast hne2
    let pt := (st.1.dropLast, st.2.dropLast)
    have hpt_len1 : pt.1.length = l - 1 := by rw [List.length_dropLast, hlen1] <;> omega
    have hpt_len2 : pt.2.length = l - 1 := by rw [List.length_dropLast, hlen2] <;> omega
    have hpt_all : pt ∈ allPairs (l - 1) := by
      simp [allPairs, binaryStrings_mem, hpt_len1, hpt_len2]
    have hsub1 : (block A st.1).Sublist (block A pt.1) := block_child_sublist_parent (A := A) (s := st.1) hne1
    have hsub2 : (block B st.2).Sublist (block B pt.2) := block_child_sublist_parent (A := B) (s := st.2) hne2
    have hI_sub : ((block A st.1).toFinset ∩ (block B st.2).toFinset) ⊆ ((block A pt.1).toFinset ∩ (block B pt.2).toFinset) :=
      Finset.inter_subset_inter (h_sublist_to_finset hsub1) (h_sublist_to_finset hsub2)
    have hpt_R_pos : blockPairR A B pt.1 pt.2 > 0 := by
      have h_nonempty : ((block A st.1).toFinset ∩ (block B st.2).toFinset).Nonempty := Finset.card_pos.mp hR_pos
      have h : ((block A pt.1).toFinset ∩ (block B pt.2).toFinset).Nonempty := h_nonempty.mono hI_sub
      exact Finset.card_pos.mpr h
    have hpt_notIR : ¬isPairIR A B pt := by
      intro hIR
      have h_st_eq : st = (pt.1 ++ [b1], pt.2 ++ [b2]) := by
        exact Prod.ext (List.dropLast_append_getLast hne1).symm (List.dropLast_append_getLast hne2).symm
      have h_goal : isPairIR A B st := by
        rw [h_st_eq]; exact ir_children_are_ir hA hB hIR b1 b2
      exact hnotIR h_goal
    have hpt_sing : pt ∈ P := Finset.mem_filter.mpr ⟨hpt_all, hpt_R_pos, hpt_notIR⟩
    have h_st_child : st ∈ childrenOf pt := by
      have h_st_eq : st = (pt.1 ++ [b1], pt.2 ++ [b2]) := by
        exact Prod.ext (List.dropLast_append_getLast hne1).symm (List.dropLast_append_getLast hne2).symm
      rw [h_st_eq]; cases b1 <;> cases b2 <;> simp [childrenOf] <;> tauto
    exact Finset.mem_biUnion.mpr ⟨pt, hpt_sing, h_st_child⟩
  have h3 : Disjoint newIR (singularPairs A B l) := by
    rw [Finset.disjoint_left]; intro st hst1 hst2
    have hIR : isPairIR A B st := (Finset.mem_filter.mp hst1).2
    have hnotIR : ¬isPairIR A B st := (Finset.mem_filter.mp hst2).2.2
    exact hnotIR hIR
  have h4 : ∀ c ∈ rest, r c = 0 := by
    intro c hc
    have hc' : c ∈ children_set := (Finset.mem_sdiff.mp hc).1
    have hnotUnion : c ∉ newIR ∪ singularPairs A B l := (Finset.mem_sdiff.mp hc).2
    have hnotIR : c ∉ newIR := by intro h; exact hnotUnion (Finset.mem_union_left _ h)
    have hnotSing : c ∉ singularPairs A B l := by intro h; exact hnotUnion (Finset.mem_union_right _ h)
    have h_notIR_prop : ¬isPairIR A B c := by
      intro hIR
      have h_in : c ∈ newIR := Finset.mem_filter.mpr ⟨hc', hIR⟩
      exact hnotIR h_in
    have h_notRpos : ¬(blockPairR A B c.1 c.2 > 0) := by
      by_contra h
      have h_sing : c ∈ singularPairs A B l := Finset.mem_filter.mpr ⟨h_children_all hc', h, h_notIR_prop⟩
      exact hnotSing h_sing
    have h : blockPairR A B c.1 c.2 = 0 := by omega
    simpa [r] using congr_arg (fun x : ℕ => (x : ℝ)) h
  have h_union_subset : newIR ∪ singularPairs A B l ⊆ children_set := by
    intro x hx
    rcases Finset.mem_union.mp hx with (hx | hx)
    · exact (Finset.mem_filter.mp hx).1
    · exact h2 hx
  have h_sum_rest : ∑ c ∈ rest, r c = 0 := by
    apply Finset.sum_eq_zero; intro c hc; exact h4 c hc
  have h_sum_decomp : ∑ c ∈ children_set, r c = ∑ c ∈ newIR, r c + ∑ c ∈ singularPairs A B l, r c := by
    have h_eq_set : children_set = (newIR ∪ singularPairs A B l) ∪ rest := by
      rw [Finset.union_sdiff_of_subset h_union_subset]
    rw [h_eq_set, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_union h3, h_sum_rest] <;> ring
  have h_s_l : ∑ c ∈ singularPairs A B l, r c = singularIntersection A B l := by rfl
  have h_decrease : singularIntersection A B (l - 1) - singularIntersection A B l = ∑ c ∈ newIR, r c := by
    have h_eq : singularIntersection A B (l - 1) = ∑ c ∈ newIR, r c + singularIntersection A B l := by
      calc
        singularIntersection A B (l - 1)
          = ∑ c ∈ children_set, r c := h1.symm
        _ = ∑ c ∈ newIR, r c + ∑ c ∈ singularPairs A B l, r c := h_sum_decomp
        _ = ∑ c ∈ newIR, r c + singularIntersection A B l := by rw [h_s_l]
    linarith
  have h_newIR_sub : newIR ⊆ allPairs l := (Finset.filter_subset _ _).trans h_children_all
  have h_good_real : ∀ (s t : List Bool), 0 ≤ (blockPairR A B s t : ℝ) - (blockPairC A B s t : ℝ) := by
    intro s t; have h := h_good s t; exact_mod_cast h
  have h61 : ∑ c ∈ allPairs l, (r c - (blockPairC A B c.1 c.2 : ℝ)) ≥ ∑ c ∈ newIR, (r c - (blockPairC A B c.1 c.2 : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h_newIR_sub
    intro i _ _; exact h_good_real i.1 i.2
  have h62 : ∀ c ∈ newIR, (r c - (blockPairC A B c.1 c.2 : ℝ)) = r c ^ 2 := by
    intro c hc
    have hIR : isPairIR A B c := (Finset.mem_filter.mp hc).2
    have h_eq_int : (blockPairR A B c.1 c.2 : ℤ) - blockPairC A B c.1 c.2 = (blockPairR A B c.1 c.2 : ℤ)^2 :=
      ir_pair_r_minus_c hA hB hIR
    have h_eq_real : ((blockPairR A B c.1 c.2 : ℝ) - (blockPairC A B c.1 c.2 : ℝ)) = (blockPairR A B c.1 c.2 : ℝ)^2 := by
      norm_cast at h_eq_int ⊢ <;> exact h_eq_int
    simpa [r] using h_eq_real
  have h63 : ∑ c ∈ newIR, (r c - (blockPairC A B c.1 c.2 : ℝ)) = ∑ c ∈ newIR, r c ^ 2 := by
    apply Finset.sum_congr rfl; intro c hc; exact h62 c hc
  have h6 : goodContribution A B l ≥ ∑ c ∈ newIR, r c ^ 2 := by
    rw [h63] at h61; exact h61
  have h7 : (newIR.card : ℝ) ≤ 4 * (M : ℝ) := by
    have h71 : newIR.card ≤ children_set.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h72 : children_set.card = ∑ pt ∈ P, (childrenOf pt).card := by
      rw [Finset.card_biUnion]
      · intro pt1 _ pt2 _ hne; exact childrenOf_disjoint hne
    have h73 : ∑ pt ∈ P, (childrenOf pt).card = 4 * P.card := by
      have h74 : ∀ pt ∈ P, (childrenOf pt).card = 4 := by intro pt _; exact childrenOf_card pt
      rw [Finset.sum_congr rfl h74]; simp [Finset.sum_const]; ring
    rw [h72, h73] at h71
    have h75 : P.card ≤ M := by
      by_cases h_l1 : l = 1
      · subst h_l1
        have h1 : P ⊆ allPairs 0 := Finset.filter_subset _ _
        have h2 : allPairs 0 = {([], [])} := by
          simp [allPairs, binaryStrings] <;> ext ⟨x, y⟩ <;> simp [binaryStrings_mem] <;> omega
        rw [h2] at h1
        have h3 : P.card ≤ 1 := Finset.card_le_card h1
        have h4 : (1 : ℕ) ≤ M := by exact_mod_cast hM_pos
        omega
      · have h_gt1 : l > 1 := by omega
        exact h_singular (l - 1) (by omega)
    have h76 : 4 * P.card ≤ 4 * M := by gcongr
    exact_mod_cast h71.trans h76
  have h_cs : (∑ c ∈ newIR, r c) ^ 2 ≤ (newIR.card : ℝ) * ∑ c ∈ newIR, r c ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := newIR) (f := r)
  have h_sum_newIR_nonneg : 0 ≤ ∑ c ∈ newIR, r c := by
    apply Finset.sum_nonneg; intro c _; positivity
  by_cases h_card : newIR.card = 0
  · have h_empty : newIR = ∅ := Finset.card_eq_zero.mp h_card
    have h_sum0 : ∑ c ∈ newIR, r c = 0 := by
      rw [h_empty]; simp
    have h_gc_nonneg : 0 ≤ goodContribution A B l := by
      apply Finset.sum_nonneg
      intro st _
      have h3 : (blockPairR A B st.1 st.2 : ℤ) - blockPairC A B st.1 st.2 ≥ 0 := h_good st.1 st.2
      exact_mod_cast h3
    have h_goal : goodContribution A B l ≥ (singularIntersection A B (l - 1) - singularIntersection A B l)^2 / (4 * M : ℝ) := by
      rw [h_decrease, h_sum0]
      simp
      exact h_gc_nonneg
    exact h_goal
  · have h_pos_card : 0 < (newIR.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h_card)
    have h_bound1 : ∑ c ∈ newIR, r c ^ 2 ≥ (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) := by
      calc
        ∑ c ∈ newIR, r c ^ 2
          = ((newIR.card : ℝ) * ∑ c ∈ newIR, r c ^ 2) / (newIR.card : ℝ) := by
            field_simp [h_pos_card.ne'] <;> ring
        _ ≥ (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) := by
          have h_simp : ((newIR.card : ℝ) * ∑ c ∈ newIR, r c ^ 2) / (newIR.card : ℝ) = ∑ c ∈ newIR, r c ^ 2 := by
            field_simp [h_pos_card.ne'] <;> ring
          rw [h_simp]
          have h_div : (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) ≤ ∑ c ∈ newIR, r c ^ 2 := by
            calc
              (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ)
                ≤ ((newIR.card : ℝ) * ∑ c ∈ newIR, r c ^ 2) / (newIR.card : ℝ) := by gcongr
              _ = ∑ c ∈ newIR, r c ^ 2 := by field_simp [h_pos_card.ne'] <;> ring
          exact h_div
    have h_sq_nonneg : 0 ≤ (∑ c ∈ newIR, r c) ^ 2 := by positivity
    have h_bound2 : (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) ≥ (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) := by
      have h_c_pos : 0 < (4 * (M : ℝ)) := by positivity
      have h : (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) ≤ (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) := by
        have h_diff : (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) - (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) ≥ 0 := by
          have h_eq : (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) - (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) =
              (∑ c ∈ newIR, r c) ^ 2 * ((4 * (M : ℝ)) - (newIR.card : ℝ)) / ((newIR.card : ℝ) * (4 * (M : ℝ))) := by
            field_simp [h_pos_card.ne', h_c_pos.ne'] <;> ring
          rw [h_eq]
          apply div_nonneg
          · exact mul_nonneg h_sq_nonneg (sub_nonneg.mpr h7)
          · exact mul_nonneg (by positivity) (by positivity)
        linarith
      exact h
    have h_final : ∑ c ∈ newIR, r c ^ 2 ≥ (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) := by
      calc
        ∑ c ∈ newIR, r c ^ 2 ≥ (∑ c ∈ newIR, r c) ^ 2 / (newIR.card : ℝ) := h_bound1
        _ ≥ (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) := h_bound2
    calc
      goodContribution A B l
        ≥ ∑ c ∈ newIR, r c ^ 2 := h6
      _ ≥ (∑ c ∈ newIR, r c) ^ 2 / (4 * (M : ℝ)) := h_final
      _ = (singularIntersection A B (l - 1) - singularIntersection A B l) ^ 2 / (4 * (M : ℝ)) := by
        rw [h_decrease]

/-! ### Main theorem -/

/--
Main direct bound theorem.

Given good contribution and at most M singular pairs per level,
proves S ≤ pW - p²/(4M * V).
-/
theorem direct_bound_with_assumptions {d : ℕ} {A B : List α}
    (hA : A.Nodup) (hB : B.Nodup)
    (hlenA : A.length = d) (hlenB : B.length = d)
    (alphabet : Finset α)
    (halphA : ∀ x ∈ A, x ∈ alphabet) (halphB : ∀ x ∈ B, x ∈ alphabet)
    (k : ℕ) (hk_pos : 0 < k) (hk : 2^k ≥ d)
    (w : ℕ → ℝ) (hw_pos : ∀ l ∈ Finset.Icc 1 k, 0 < w l)
    (M : ℕ) (hM_pos : 0 < M)
    (h_good : GoodContributionHyp A B)
    (h_singular : SingularCountHyp A B M) :
    let p : ℝ := (A.toFinset ∩ B.toFinset).card
    let W : ℝ := ∑ l ∈ Finset.Icc 1 k, w l
    let V : ℝ := ∑ l ∈ Finset.Icc 1 k, 1 / w l
    ∑ l ∈ Finset.Icc 1 k, w l *
      (∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ)) ≤
    p * W - p^2 / ((4 * M : ℝ) * V) := by
  let p : ℝ := (A.toFinset ∩ B.toFinset).card
  let W : ℝ := ∑ l ∈ Finset.Icc 1 k, w l
  let V : ℝ := ∑ l ∈ Finset.Icc 1 k, 1 / w l
  have h_level : ∀ l ∈ Finset.Icc 1 k,
      (∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ)) =
      ∑ st ∈ allPairs l, (blockPairC A B st.1 st.2 : ℝ) := by
    intro l _; exact level_sum_decomposition hA hB l alphabet halphA halphB
  have h_total_r : ∀ l, ∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ) = p := by
    intro l; exact sum_blockPairR_eq hA hB l
  have h_sk : singularIntersection A B k = 0 := by
    have h1 : ∀ st ∈ singularPairs A B k, False := by
      intro st hst
      have h2 : st ∈ allPairs k := (Finset.mem_filter.mp hst).1
      have h3 : st.1.length = k := binaryStrings_mem.mp (Finset.mem_product.mp h2).1
      have h4 : st.2.length = k := binaryStrings_mem.mp (Finset.mem_product.mp h2).2
      have h5 : isPairIR A B st := all_pairs_ir_at_level_k hA hB hlenA hlenB hk h3 h4
      have h6 : blockPairR A B st.1 st.2 > 0 ∧ ¬isPairIR A B st := (Finset.mem_filter.mp hst).2
      exact h6.2 h5
    have h_empty : singularPairs A B k = ∅ := by
      by_contra h
      have h_ne : (singularPairs A B k).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      rcases h_ne with ⟨st, hst⟩
      exact h1 st hst
    unfold singularIntersection; rw [h_empty] <;> simp
  have h_s_decr : ∀ l ∈ Finset.Icc 1 k, singularIntersection A B l ≤ singularIntersection A B (l - 1) := by
    intro l hl; have h1 : 0 < l := (Finset.mem_Icc.mp hl).1; exact singularIntersection_decr hA hB h1
  have h_Q_bound : ∀ l ∈ Finset.Icc 1 k,
      goodContribution A B l ≥ (singularIntersection A B (l - 1) - singularIntersection A B l)^2 / (4 * M : ℝ) := by
    intro l hl
    have h1 : 0 < l := (Finset.mem_Icc.mp hl).1
    exact good_contribution_bound hA hB M hM_pos h_good h_singular h1
  let S : ℝ := ∑ l ∈ Finset.Icc 1 k, w l *
      (∑ a ∈ alphabet, ∑ b ∈ alphabet.erase a,
        (ConcreteBlockSum.G A l a b : ℝ) * (ConcreteBlockSum.G B l a b : ℝ))
  have h_all0 : allPairs 0 = {([], [])} := by
    simp [allPairs, binaryStrings] <;> ext ⟨x, y⟩ <;> simp [binaryStrings_mem] <;> omega
  have h_good_nonneg : ∀ l, 0 ≤ goodContribution A B l := by
    intro l
    apply Finset.sum_nonneg
    intro st _
    have h3 : (blockPairR A B st.1 st.2 : ℤ) - blockPairC A B st.1 st.2 ≥ 0 := h_good st.1 st.2
    exact_mod_cast h3
  have h_sum_conv : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l = p * W - S := by
    have h1 : ∀ l, goodContribution A B l =
        (∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ)) -
        (∑ st ∈ allPairs l, (blockPairC A B st.1 st.2 : ℝ)) := by
      intro l
      have h : goodContribution A B l =
          ∑ st ∈ allPairs l, ((blockPairR A B st.1 st.2 : ℝ) - (blockPairC A B st.1 st.2 : ℝ)) := by rfl
      rw [h, Finset.sum_sub_distrib]
    have h2 : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l =
        ∑ l ∈ Finset.Icc 1 k, (w l * (∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ)) -
          w l * (∑ st ∈ allPairs l, (blockPairC A B st.1 st.2 : ℝ))) := by
      apply Finset.sum_congr rfl; intro l hl; rw [h1 l, mul_sub]
    rw [h2, Finset.sum_sub_distrib]
    have h3 : ∑ l ∈ Finset.Icc 1 k, w l * (∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ)) = p * W := by
      calc
        ∑ l ∈ Finset.Icc 1 k, w l * (∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ))
          = ∑ l ∈ Finset.Icc 1 k, w l * p := by
            apply Finset.sum_congr rfl; intro l hl; rw [h_total_r l]
        _ = (∑ l ∈ Finset.Icc 1 k, w l) * p := by rw [Finset.sum_mul]
        _ = p * W := by ring
    have h5 : ∑ l ∈ Finset.Icc 1 k, w l * (∑ st ∈ allPairs l, (blockPairC A B st.1 st.2 : ℝ)) = S := by
      apply Finset.sum_congr rfl; intro l hl; rw [h_level l hl]
    rw [h3, h5] <;> ring
  by_cases hp0 : p = 0
  · -- p = 0 case: goodContribution ≥ 0 implies S ≤ 0
    have h_sum_nonneg : 0 ≤ ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l := by
      apply Finset.sum_nonneg
      intro l hl
      have hwl : 0 ≤ w l := by linarith [hw_pos l hl]
      have hgc : 0 ≤ goodContribution A B l := h_good_nonneg l
      exact mul_nonneg hwl hgc
    have h9 : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l = p * W - S := h_sum_conv
    have h10 : 0 ≤ p * W - S := by
      rw [←h9]
      exact h_sum_nonneg
    have h11 : p = 0 := hp0
    rw [h11] at h10
    have h12 : S ≤ 0 := by linarith
    have h13 : (A.toFinset ∩ B.toFinset).card = 0 := by
      have h14 : p = ((A.toFinset ∩ B.toFinset).card : ℝ) := by rfl
      rw [h14] at h11
      exact_mod_cast h11
    simpa [h13] using h12
  · -- p > 0 case
    have hp_pos : 0 < p := by
      have h_nonneg : 0 ≤ p := by positivity
      exact lt_of_le_of_ne h_nonneg (Ne.symm hp0)
    by_cases h0_sing : singularPairs A B 0 = ∅
    · -- Case: level-0 pair is IR (singularPairs 0 = ∅)
      have h_card_pos : 0 < (A.toFinset ∩ B.toFinset).card := by
        by_contra h
        have h' : (A.toFinset ∩ B.toFinset).card = 0 := by omega
        have h'' : p = 0 := by simpa [p] using h'
        exact hp0 h''
      have h_rpos : blockPairR A B [] [] > 0 := by
        have h_eq : blockPairR A B [] [] = (A.toFinset ∩ B.toFinset).card := by
          simp [blockPairR, block]
        rw [h_eq]
        exact h_card_pos
      have hIR0 : isPairIR A B ([], []) := by
        have h_in : ([], []) ∈ allPairs 0 := by rw [h_all0] <;> simp
        by_contra hIR
        have h_sing : ([], []) ∈ singularPairs A B 0 := by
          exact Finset.mem_filter.mpr ⟨h_in, h_rpos, hIR⟩
        rw [h0_sing] at h_sing
        <;> simp at h_sing
      have h_all_ir : ∀ l (st : List Bool × List Bool), st ∈ allPairs l → isPairIR A B st :=
        all_pairs_ir_of_level0_ir hA hB hIR0
      have h_gc : ∀ l, goodContribution A B l = ∑ st ∈ allPairs l, (blockPairR A B st.1 st.2 : ℝ)^2 := by
        intro l
        apply Finset.sum_congr rfl
        intro st hst
        have hIR : isPairIR A B st := h_all_ir l st hst
        have h : (blockPairR A B st.1 st.2 : ℝ) - (blockPairC A B st.1 st.2 : ℝ) =
            (blockPairR A B st.1 st.2 : ℝ)^2 := by
          exact_mod_cast ir_pair_r_minus_c hA hB hIR
        exact h
      let s : ℕ → ℝ := fun l => if l = 0 then p else 0
      have hs0 : p ≤ s 0 := by simp [s]
      have hsk : s k = 0 := by
        have h : k ≠ 0 := by linarith
        have h' : s k = 0 := by
          dsimp only [s]
          rw [if_neg h] <;> ring
        exact h'
      have hs_nonneg : ∀ l, 0 ≤ s l := by
        intro l; by_cases h : l = 0 <;> simp [s, h] <;> positivity
      have hs_decr : ∀ l ∈ Finset.Icc 1 k, s l ≤ s (l - 1) := by
        intro l hl
        have h_pos : 0 < l := (Finset.mem_Icc.mp hl).1
        by_cases h : l = 1
        · subst h
          have h_pos2 : 0 ≤ p := by positivity
          simpa [s] using h_pos2
        · have h_gt1 : l > 1 := by omega
          have h_ne2 : l - 1 ≠ 0 := by omega
          have h_lne0 : l ≠ 0 := by omega
          simp [s, h_ne2, h_lne0]
      have hQ : ∀ l ∈ Finset.Icc 1 k, goodContribution A B l ≥ (s (l - 1) - s l)^2 / ((4 * M : ℕ) : ℝ) := by
        intro l hl
        have h_pos : 0 < l := (Finset.mem_Icc.mp hl).1
        by_cases h : l = 1
        · subst h
          rw [h_gc 1]
          have h4 : ∑ st ∈ allPairs 1, (blockPairR A B st.1 st.2 : ℝ) = p := h_total_r 1
          have h5 : (allPairs 1).card = 4 := by simp [allPairs, binaryStrings] <;> decide
          have h_cs := sq_sum_le_card_mul_sum_sq (s := allPairs 1)
            (f := fun st : List Bool × List Bool => (blockPairR A B st.1 st.2 : ℝ))
          rw [h4, h5] at h_cs
          have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M from hM_pos)
          have h_goal : ∑ st ∈ allPairs 1, (blockPairR A B st.1 st.2 : ℝ)^2 ≥ p^2 / ((4 * M : ℕ) : ℝ) := by
            have h6 : p^2 ≤ (4 : ℝ) * ∑ st ∈ allPairs 1, (blockPairR A B st.1 st.2 : ℝ)^2 := h_cs
            have h7 : ∑ st ∈ allPairs 1, (blockPairR A B st.1 st.2 : ℝ)^2 ≥ p^2 / 4 := by linarith
            have h8 : p^2 / 4 ≥ p^2 / ((4 * M : ℕ) : ℝ) := by
              have h9 : (4 : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by norm_cast <;> omega
              exact div_le_div_of_nonneg_left (by positivity) (by positivity) h9
            linarith
          simpa [s] using h_goal
        · have h_gt1 : l > 1 := by omega
          have h_ne2 : l - 1 ≠ 0 := by omega
          have h_lne0 : l ≠ 0 := by omega
          have h_s1 : s (l - 1) = 0 := by
            dsimp only [s]; rw [if_neg h_ne2] <;> ring
          have h_s2 : s l = 0 := by
            dsimp only [s]; rw [if_neg h_lne0] <;> ring
          have h6 : (s (l - 1) - s l)^2 / ((4 * M : ℕ) : ℝ) = 0 := by
            rw [h_s1, h_s2] <;> ring
          rw [h6]
          exact h_good_nonneg l
      have h_main : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l ≥ p^2 / (((4 * M : ℕ) : ℝ) * V) :=
        SingularPairs.telescoping_cs_bound_K (4 * M) (by positivity)
          k w hw_pos (goodContribution A B) s p hQ (by positivity) hs0 hsk hs_nonneg hs_decr hk_pos
      have h9 : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l = p * W - S := h_sum_conv
      rw [h9] at h_main
      have h_cast : ((4 * M : ℕ) : ℝ) = (4 * M : ℝ) := by norm_cast
      rw [h_cast] at h_main
      linarith
    · -- Case: level-0 pair is singular
      have h3 : singularPairs A B 0 ⊆ allPairs 0 := Finset.filter_subset _ _
      rw [h_all0] at h3
      have h4 : (singularPairs A B 0).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0_sing
      rcases h4 with ⟨x, hx⟩
      have h5 : x ∈ ({([], [])} : Finset (List Bool × List Bool)) := h3 hx
      have h6 : x = ([], []) := by simpa using h5
      have h_sing0 : singularPairs A B 0 = {([], [])} := by
        have h7 : singularPairs A B 0 ⊆ {([], [])} := h3
        have h8 : {([], [])} ⊆ singularPairs A B 0 := by
          rw [Finset.singleton_subset_iff]
          rw [h6] at hx
          exact hx
        exact Finset.Subset.antisymm h7 h8
      have h_s0 : singularIntersection A B 0 = p := by
        unfold singularIntersection
        rw [h_sing0]
        have h5 : blockPairR A B [] [] = (A.toFinset ∩ B.toFinset).card := by
          simp [blockPairR, block]
        simp [h5] <;> norm_cast
      let s : ℕ → ℝ := singularIntersection A B
      have hs0 : p ≤ s 0 := by
        dsimp only [s]
        rw [h_s0]
        <;> exact le_refl p
      have hsk : s k = 0 := h_sk
      have hs_nonneg : ∀ l, 0 ≤ s l := by
        intro l; exact Finset.sum_nonneg (fun _ _ => by positivity)
      have hs_decr : ∀ l ∈ Finset.Icc 1 k, s l ≤ s (l - 1) := h_s_decr
      have hQ : ∀ l ∈ Finset.Icc 1 k, goodContribution A B l ≥ (s (l - 1) - s l)^2 / ((4 * M : ℕ) : ℝ) := by
        intro l hl
        have h := h_Q_bound l hl
        have h_cast : (4 * M : ℝ) = ((4 * M : ℕ) : ℝ) := by norm_cast
        rw [h_cast] at h
        exact h
      have h_main : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l ≥ p^2 / (((4 * M : ℕ) : ℝ) * V) :=
        SingularPairs.telescoping_cs_bound_K (4 * M) (by positivity)
          k w hw_pos (goodContribution A B) s p hQ (by positivity) hs0 hsk hs_nonneg hs_decr hk_pos
      have h9 : ∑ l ∈ Finset.Icc 1 k, w l * goodContribution A B l = p * W - S := h_sum_conv
      rw [h9] at h_main
      have h_cast : ((4 * M : ℕ) : ℝ) = (4 * M : ℝ) := by norm_cast
      rw [h_cast] at h_main
      linarith

end MarcusTardos.DirectBoundFramework
