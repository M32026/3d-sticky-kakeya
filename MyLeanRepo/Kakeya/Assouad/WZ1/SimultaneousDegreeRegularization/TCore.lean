import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# T-core existence for m-partite hypergraphs

Given finite coordinate maps `parent k : I → J k` and thresholds `T k`,
iteratively remove entire fibers that fall below threshold until every
nonempty fiber has size at least `T k`.  The number of removed edges is
bounded by `∑_k T k * |image(parent k)|`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A subset `S'` is a T-core if every nonempty fiber at each scale has
size at least the threshold `T k`. -/
def IsTCore {I : Type*} [DecidableEq I] {m : ℕ}
    {J : Fin m → Type*} [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (T : Fin m → ℕ) (S : Finset I) : Prop :=
  ∀ (k : Fin m) (j : J k),
    0 < (S.filter (fun i => parent k i = j)).card →
      T k ≤ (S.filter (fun i => parent k i = j)).card

/-- Capacity of a set: `∑_k T k * |image(parent k)|`. -/
def capacity {I : Type*} [DecidableEq I] {m : ℕ}
    {J : Fin m → Type*} [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (T : Fin m → ℕ) (S : Finset I) : ℕ :=
  ∑ k : Fin m, T k * (S.image (parent k)).card

/-- Helper: sum over univ decomposes as f k + sum over erase k. -/
private lemma sum_univ_split {m : ℕ} (k : Fin m) (f : Fin m → ℕ) :
    ∑ l : Fin m, f l = f k + ∑ l ∈ Finset.univ.erase k, f l := by
  have h_notin : k ∉ Finset.univ.erase k := by simp
  have h_univ_eq : (Finset.univ : Finset (Fin m)) = insert k (Finset.univ.erase k) := by
    ext x; simp <;> tauto
  have h_congr : ∑ l ∈ (Finset.univ : Finset (Fin m)), f l =
      ∑ l ∈ insert k (Finset.univ.erase k), f l :=
    Finset.sum_congr h_univ_eq (fun _ _ => rfl)
  have h_sum_insert : ∑ l ∈ insert k (Finset.univ.erase k), f l =
      f k + ∑ l ∈ Finset.univ.erase k, f l := by
    rw [Finset.sum_insert h_notin] <;> rfl
  rw [h_congr, h_sum_insert]

/-- Removing a bad fiber decreases capacity by at least T k. -/
private lemma capacity_decrease {I : Type*} [DecidableEq I]
    {m : ℕ} {J : Fin m → Type*} [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (T : Fin m → ℕ)
    (X : Finset I) (k : Fin m) (j : J k)
    (h_j_in_image : j ∈ X.image (parent k)) :
    let F := X.filter (fun i => parent k i = j)
    let X1 := X \ F
    capacity parent T X1 + T k ≤ capacity parent T X := by
  classical
  let F := X.filter (fun i => parent k i = j)
  let X1 := X \ F
  have h_image_k : X1.image (parent k) = X.image (parent k) \ {j} := by
    ext x
    simp only [X1, Finset.mem_image, Finset.mem_sdiff, Finset.mem_singleton]
    <;> aesop
  have h_card_k : (X1.image (parent k)).card = (X.image (parent k)).card - 1 := by
    rw [h_image_k]
    have h_sub : ({j} : Finset (J k)) ⊆ X.image (parent k) := by
      simp [h_j_in_image]
    have h : (X.image (parent k) \ {j}).card = (X.image (parent k)).card - 1 := by
      rw [Finset.card_sdiff_of_subset h_sub]
      <;> simp
    exact h
  have h_other : ∀ l ∈ Finset.univ.erase k,
      (X1.image (parent l)).card ≤ (X.image (parent l)).card := by
    intro l _
    have h5 : X1.image (parent l) ⊆ X.image (parent l) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have h7 : i ∈ X ∧ i ∉ F := by simpa [X1, Finset.mem_sdiff] using hi
      exact Finset.mem_image.mpr ⟨i, h7.1, rfl⟩
    exact Finset.card_le_card h5
  simp only [capacity]
  let f1 : Fin m → ℕ := fun l => T l * (X1.image (parent l)).card
  let f2 : Fin m → ℕ := fun l => T l * (X.image (parent l)).card
  have h_sum1 : ∑ l : Fin m, f1 l = f1 k + ∑ l ∈ Finset.univ.erase k, f1 l :=
    sum_univ_split k f1
  have h_sum2 : ∑ l : Fin m, f2 l = f2 k + ∑ l ∈ Finset.univ.erase k, f2 l :=
    sum_univ_split k f2
  rw [h_sum1, h_sum2]
  have h_k : f1 k + T k = f2 k := by
    dsimp only [f1, f2]
    rw [h_card_k]
    have h2 : 0 < (X.image (parent k)).card := Finset.card_pos.mpr ⟨j, h_j_in_image⟩
    have h3 : T k * ((X.image (parent k)).card - 1) + T k =
        T k * (((X.image (parent k)).card - 1) + 1) := by ring
    rw [h3]
    have h4 : (X.image (parent k)).card - 1 + 1 = (X.image (parent k)).card := by omega
    rw [h4]
  have h5 : ∑ l ∈ Finset.univ.erase k, f1 l ≤ ∑ l ∈ Finset.univ.erase k, f2 l :=
    Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_left (h_other l hl) (by positivity))
  have h6 : f1 k + ∑ l ∈ Finset.univ.erase k, f1 l + T k =
      (f1 k + T k) + ∑ l ∈ Finset.univ.erase k, f1 l := by ring
  rw [h6, h_k]
  linarith

/--
T-core existence: every finite set `S` has a maximal T-core subfamily `S'`.
The removed edges are bounded by `capacity parent T S`.
-/
lemma t_core_existence {I : Type*} [DecidableEq I]
    {m : ℕ} {J : Fin m → Type*} [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (T : Fin m → ℕ) (S : Finset I) :
    ∃ (S' : Finset I),
      S' ⊆ S ∧
      IsTCore parent T S' ∧
      (S \ S').card ≤ capacity parent T S := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (X : Finset I), X.card ≤ n →
      ∃ (S' : Finset I), S' ⊆ X ∧ IsTCore parent T S' ∧
        (X \ S').card ≤ capacity parent T X
  have h_main : ∀ (n : ℕ), (∀ (m : ℕ), m < n → P m) → P n := by
    intro n ih X hX_card
    by_cases h_core : IsTCore parent T X
    · exact ⟨X, by simp, h_core, by simp⟩
    · have h_bad : ∃ (k : Fin m) (j : J k),
          0 < (X.filter (fun i => parent k i = j)).card ∧
          (X.filter (fun i => parent k i = j)).card < T k := by
        simpa [IsTCore] using h_core
      rcases h_bad with ⟨k, j, hj_pos, hj_lt⟩
      let F := X.filter (fun i => parent k i = j)
      let X1 := X \ F
      have hF_sub : F ⊆ X := Finset.filter_subset _ _
      have hF_pos : 0 < F.card := hj_pos
      have h_j_in_image : j ∈ X.image (parent k) := by
        rcases Finset.card_pos.mp hj_pos with ⟨i, hi⟩
        have hpi : parent k i = j := (Finset.mem_filter.mp hi).2
        exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, hpi⟩
      have hX1_lt : X1.card < X.card := by
        have h_card : X1.card = X.card - F.card := by
          rw [show X1 = X \ F from rfl]
          rw [Finset.card_sdiff]
          have h_inter : F ∩ X = F := by
            rw [Finset.inter_comm]
            exact Finset.inter_eq_right.mpr hF_sub
          rw [h_inter]
        rw [h_card]
        have hX_pos : 0 < X.card := lt_of_lt_of_le hF_pos (Finset.card_le_card hF_sub)
        exact Nat.sub_lt hX_pos hF_pos
      have hX1_lt_n : X1.card < n := by
        calc X1.card < X.card := hX1_lt
             _ ≤ n := hX_card
      rcases ih X1.card hX1_lt_n X1 (by linarith) with ⟨S', hS'_sub, hS'_core, h_bound⟩
      have hX1_sub_X : X1 ⊆ X := by
        simpa [X1] using Finset.sdiff_subset (s := X) (t := F)
      have hS'_sub_X : S' ⊆ X := by
        calc S' ⊆ X1 := hS'_sub
           _ ⊆ X := hX1_sub_X
      have h_cap_dec : capacity parent T X1 + T k ≤ capacity parent T X :=
        capacity_decrease parent T X k j h_j_in_image
      have hF_lt_Tk : F.card < T k := hj_lt
      have h_disj : Disjoint F (X1 \ S') := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have h6 : x ∈ X1 ∧ x ∉ S' := by simpa [Finset.mem_sdiff] using hx2
        have h7 : x ∈ X \ F := h6.1
        have h9 : x ∈ X ∧ x ∉ F := by simpa [Finset.mem_sdiff] using h7
        exact h9.2 hx1
      have h_union : X \ S' = F ∪ (X1 \ S') := by
        ext x
        simp only [X1, Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro h
          have hx_X : x ∈ X := h.1
          have hx_nS' : x ∉ S' := h.2
          by_cases hxF : x ∈ F
          · exact Or.inl hxF
          · exact Or.inr ⟨⟨hx_X, hxF⟩, hx_nS'⟩
        · rintro (hxF | ⟨⟨hx_X, _⟩, hx_nS'⟩)
          · have hx_nS' : x ∉ S' := by
              intro hxs
              have h10 : x ∈ X1 := hS'_sub hxs
              have h11 : x ∈ X ∧ x ∉ F := by simpa [X1, Finset.mem_sdiff] using h10
              exact h11.2 hxF
            exact ⟨hF_sub hxF, hx_nS'⟩
          · exact ⟨hx_X, hx_nS'⟩
      have h_removed : (X \ S').card = F.card + (X1 \ S').card := by
        rw [h_union, Finset.card_union_of_disjoint h_disj]
      have h_final : F.card + (X1 \ S').card ≤ capacity parent T X := by
        have h4 : F.card + 1 ≤ T k := by omega
        have h5 : F.card + (X1 \ S').card + 1 ≤ capacity parent T X := by
          calc
            F.card + (X1 \ S').card + 1
              = F.card + 1 + (X1 \ S').card := by ring
            _ ≤ T k + (X1 \ S').card := by gcongr
            _ ≤ T k + capacity parent T X1 := by gcongr <;> exact h_bound
            _ = capacity parent T X1 + T k := by ring
            _ ≤ capacity parent T X := h_cap_dec
        omega
      have h_goal : (X \ S').card ≤ capacity parent T X := by
        calc (X \ S').card = F.card + (X1 \ S').card := h_removed
             _ ≤ capacity parent T X := h_final
      exact ⟨S', hS'_sub_X, hS'_core, h_goal⟩
  have hP : ∀ n, P n := fun n => Nat.strong_induction_on n h_main
  exact hP S.card S (by rfl)

end Kakeya.Assouad
