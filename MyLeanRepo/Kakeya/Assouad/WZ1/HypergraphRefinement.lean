import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
WZ1 Lemma 37: hypergraph refinement via potential function deletion.
-/

namespace Kakeya.Assouad

open scoped ENNReal

section Helpers
variable {k : ℕ} {α : Type*} [DecidableEq α]

/-- Restrict an edge to coordinates in I; coordinates outside I are `none`. -/
private def wz1Restrict (I : Finset (Fin k)) (e : Fin k → α) : Fin k → Option α :=
  fun i => if i ∈ I then some (e i) else none

/-- Two edges have equal I-restrictions iff they agree on all coordinates in I. -/
private lemma wz1Restrict_eq_iff {I : Finset (Fin k)} {e f : Fin k → α} :
    wz1Restrict I e = wz1Restrict I f ↔ ∀ i ∈ I, e i = f i := by
  constructor
  · intro h i hi
    have h' := congr_fun h i
    simpa [wz1Restrict, hi] using h'
  · intro h
    funext i
    by_cases hi : i ∈ I
    · simp [wz1Restrict, hi, h i hi]
    · simp [wz1Restrict, hi]

/-- Number of distinct I-restrictions of edges in S is at most ∏_{i∈I} |A_i|. -/
private lemma restrict_count_le
    (A : Fin k → Finset α)
    (H : Finset (Fin k → α))
    (hA : ∀ edge ∈ H, ∀ i, edge i ∈ A i)
    (S : Finset (Fin k → α))
    (hS : S ⊆ H)
    (I : Finset (Fin k)) :
    (S.image (wz1Restrict I)).card ≤ ∏ i ∈ I, (A i).card := by
  let piSet : Finset ((i : Fin k) → i ∈ I → α) := Finset.pi I A
  let toRestrict : ((i : Fin k) → i ∈ I → α) → (Fin k → Option α) :=
    fun f i => if h : i ∈ I then some (f i h) else none
  let possible : Finset (Fin k → Option α) := piSet.image toRestrict
  have h_inj : Function.Injective toRestrict := by
    intro f g h
    funext i hi
    have h' := congr_fun h i
    simpa [toRestrict, hi] using h'
  have h1 : (S.image (wz1Restrict I)) ⊆ possible := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
    let f : (i : Fin k) → i ∈ I → α := fun i _ => e i
    have hf : f ∈ piSet := by
      rw [Finset.mem_pi]
      intro i hi
      exact hA e (hS he) i
    have h_eq : toRestrict f = wz1Restrict I e := by
      funext i
      by_cases hi : i ∈ I <;> simp [toRestrict, wz1Restrict, f, hi]
    exact Finset.mem_image.mpr ⟨f, hf, h_eq⟩
  have h2 : possible.card = piSet.card :=
    Finset.card_image_of_injective piSet h_inj
  have h3 : piSet.card = ∏ i ∈ I, (A i).card := Finset.card_pi I A
  calc
    (S.image (wz1Restrict I)).card ≤ possible.card := Finset.card_le_card h1
    _ = piSet.card := h2
    _ = ∏ i ∈ I, (A i).card := h3

/-- Deleting the entire I-fiber of e removes exactly one I-restriction. -/
private lemma fiber_deletion_count_eq
    (S : Finset (Fin k → α))
    (I : Finset (Fin k))
    (e : Fin k → α)
    (he : e ∈ S) :
    let F := wz1HypergraphFiber S I e
    ((S \ F).image (wz1Restrict I)).card =
      (S.image (wz1Restrict I)).card - 1 := by
  let F := wz1HypergraphFiber S I e
  have h_main : (S \ F).image (wz1Restrict I) =
      (S.image (wz1Restrict I)).erase (wz1Restrict I e) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨f, hf, rfl⟩
      have hf1 : f ∈ S := (Finset.mem_sdiff.mp hf).1
      have hf2 : f ∉ F := (Finset.mem_sdiff.mp hf).2
      have hne : wz1Restrict I f ≠ wz1Restrict I e := by
        intro h
        have h_agree : ∀ i ∈ I, f i = e i := wz1Restrict_eq_iff.mp h
        exact hf2 (by
          simp only [F, wz1HypergraphFiber, Finset.mem_filter] at * <;> tauto)
      exact ⟨hne, ⟨f, hf1, rfl⟩⟩
    · rintro ⟨hne, ⟨f, hf, rfl⟩⟩
      have hf2 : f ∉ F := by
        intro hF
        have h_agree : ∀ i ∈ I, f i = e i := by
          simp only [F, wz1HypergraphFiber, Finset.mem_filter] at hF <;> tauto
        have h_eq : wz1Restrict I f = wz1Restrict I e :=
          wz1Restrict_eq_iff.mpr h_agree
        exact hne h_eq
      exact ⟨f, Finset.mem_sdiff.mpr ⟨hf, hf2⟩, rfl⟩
  dsimp only
  rw [h_main]
  have h_in : wz1Restrict I e ∈ S.image (wz1Restrict I) :=
    Finset.mem_image.mpr ⟨e, he, rfl⟩
  rw [Finset.card_erase_of_mem h_in]
  <;> simp

/-- Deleting any fiber can only decrease the number of J-restrictions. -/
private lemma fiber_deletion_count_le
    (S : Finset (Fin k → α))
    (I J : Finset (Fin k))
    (e : Fin k → α) :
    let F := wz1HypergraphFiber S I e
    ((S \ F).image (wz1Restrict J)).card ≤
      (S.image (wz1Restrict J)).card := by
  let F := wz1HypergraphFiber S I e
  have h : (S \ F).image (wz1Restrict J) ⊆ S.image (wz1Restrict J) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ S := (Finset.mem_sdiff.mp hy).1
    exact Finset.mem_image.mpr ⟨y, hy', rfl⟩
  exact Finset.card_le_card h

/-- Splits a sum over all subsets into the term at I plus the rest. -/
private lemma sum_split {β : Type*} [AddCommMonoid β]
    (I : Finset (Fin k)) (f : Finset (Fin k) → β) :
    ∑ J ∈ (Finset.univ : Finset (Finset (Fin k))), f J =
    f I + ∑ J ∈ (Finset.univ \ {I}), f J := by
  have h_disj : Disjoint ({I} : Finset (Finset (Fin k))) (Finset.univ \ {I}) := by simp
  have h_union : ({I} : Finset (Finset (Fin k))) ∪ (Finset.univ \ {I}) =
      (Finset.univ : Finset (Finset (Fin k))) := by simp
  have h : ∑ J ∈ (Finset.univ : Finset (Finset (Fin k))), f J =
      ∑ J ∈ ({I} : Finset (Finset (Fin k))) ∪ (Finset.univ \ {I}), f J := by
    rw [h_union]
  rw [h, Finset.sum_union h_disj]
  <;> simp

/-- The threshold expression is finite when epsilon < 1 and P > 0. -/
private lemma threshold_finite
    {epsilon : ENNReal} (hε : epsilon < 1)
    (n : ℕ) (P : ENNReal) (hP : 0 < P) :
    (epsilon / (2 : ENNReal)^k) * (n : ENNReal) / P ≠ ⊤ := by
  have h1 : epsilon ≠ ⊤ := by
    intro h
    rw [h] at hε
    simp at hε
  have h2 : (2 : ENNReal)^k ≠ 0 := by positivity
  have h3 : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h4 : (epsilon / (2 : ENNReal)^k) ≠ ⊤ := ENNReal.div_ne_top h1 h2
  have h5 : ((epsilon / (2 : ENNReal)^k) * (n : ENNReal)) ≠ ⊤ := ENNReal.mul_ne_top h4 h3
  have hP_ne_zero : P ≠ 0 := ne_of_gt hP
  exact ENNReal.div_ne_top h5 hP_ne_zero

/-- Product of vertex class cardinalities splits across I and univ \\ I. -/
private lemma product_split (A : Fin k → Finset α) (I : Finset (Fin k)) :
    wz1VertexCardProduct A I * wz1VertexCardProduct A (Finset.univ \ I) =
    wz1VertexCardProduct A Finset.univ := by
  have h_disj : Disjoint I (Finset.univ \ I) := by simp [Finset.disjoint_left]
  have h_union : I ∪ (Finset.univ \ I) = (Finset.univ : Finset (Fin k)) := by simp
  simp only [wz1VertexCardProduct]
  rw [← Finset.prod_union h_disj, h_union]

/-- Potential decrease when restriction count at I drops by 1. -/
private lemma potential_decrease
    (card₀ card₁ : Finset (Fin k) → ℕ)
    (T : Finset (Fin k) → ENNReal)
    (I : Finset (Fin k))
    (h_eq : card₀ I = card₁ I + 1)
    (h_mono : ∀ J ≠ I, card₁ J ≤ card₀ J)
    (hT : T I ≠ ⊤) :
    ∑ J ∈ (Finset.univ : Finset (Finset (Fin k))),
      (card₁ J : ENNReal) * T J + T I ≤
    ∑ J ∈ (Finset.univ : Finset (Finset (Fin k))),
      (card₀ J : ENNReal) * T J := by
  let univ' := (Finset.univ : Finset (Finset (Fin k)))
  have h_sum₁ : ∑ J ∈ univ', (card₁ J : ENNReal) * T J =
      (card₁ I : ENNReal) * T I + ∑ J ∈ (univ' \ {I}), (card₁ J : ENNReal) * T J :=
    sum_split I (fun J => (card₁ J : ENNReal) * T J)
  have h_sum₀ : ∑ J ∈ univ', (card₀ J : ENNReal) * T J =
      (card₀ I : ENNReal) * T I + ∑ J ∈ (univ' \ {I}), (card₀ J : ENNReal) * T J :=
    sum_split I (fun J => (card₀ J : ENNReal) * T J)
  rw [h_sum₁, h_sum₀]
  have h6 : (card₀ I : ENNReal) = (card₁ I : ENNReal) + 1 := by exact_mod_cast h_eq
  rw [h6]
  have h7 : ((card₁ I : ENNReal) + 1) * T I =
      (card₁ I : ENNReal) * T I + T I := by
    rw [add_mul, one_mul]
  rw [h7]
  have h8 : ∑ J ∈ (univ' \ {I}), (card₁ J : ENNReal) * T J ≤
      ∑ J ∈ (univ' \ {I}), (card₀ J : ENNReal) * T J := by
    apply Finset.sum_le_sum
    intro J hJ
    have hJne : J ≠ I := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hJ <;> tauto
    have h9 : (card₁ J : ENNReal) ≤ (card₀ J : ENNReal) := by exact_mod_cast h_mono J hJne
    exact mul_le_mul_of_nonneg_right h9 (by simp)
  have h_rearrange : (card₁ I : ENNReal) * T I +
        ∑ J ∈ (univ' \ {I}), (card₁ J : ENNReal) * T J + T I =
      (card₁ I : ENNReal) * T I + T I +
        ∑ J ∈ (univ' \ {I}), (card₁ J : ENNReal) * T J := by
    simp [add_assoc, add_comm]
  rw [h_rearrange]
  exact add_le_add (le_refl ((card₁ I : ENNReal) * T I + T I)) h8

/-- From failure of uniform density, extract a witness with small fiber. -/
private lemma not_dense_to_exists
    {k : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin k → α))
    (T : Finset (Fin k) → ENNReal)
    (hDense : ¬ ∀ e ∈ S, ∀ (I : Finset (Fin k)),
      T I ≤ ((wz1HypergraphFiber S I e).card : ENNReal)) :
    ∃ (e : Fin k → α), e ∈ S ∧ ∃ (I : Finset (Fin k)),
      ((wz1HypergraphFiber S I e).card : ENNReal) < T I := by
  classical
  by_contra h
  have h_dense : ∀ e ∈ S, ∀ (I : Finset (Fin k)),
      T I ≤ ((wz1HypergraphFiber S I e).card : ENNReal) := by
    intro e he I
    by_cases h6 : T I ≤ ((wz1HypergraphFiber S I e).card : ENNReal)
    · exact h6
    · have h7 : ((wz1HypergraphFiber S I e).card : ENNReal) < T I := lt_of_not_ge h6
      have h8 : ∃ (e' : Fin k → α), e' ∈ S ∧ ∃ (I' : Finset (Fin k)),
          ((wz1HypergraphFiber S I' e').card : ENNReal) < T I' := ⟨e, he, I, h7⟩
      exfalso
      exact h h8
  exact hDense h_dense

end Helpers

theorem wz1_hypergraph_refinement :
    WZ1HypergraphRefinementStatement := by
  intro k α _ A H hH epsilon hε_pos hε_lt_one
  classical
  by_cases hH_empty : H = ∅
  · subst hH_empty
    refine' ⟨∅, by simp, by simp, _⟩
    constructor
    · intro edge h; simp at h
    · intro edge h; simp at h
  · rcases Finset.nonempty_iff_ne_empty.mpr hH_empty with ⟨e0, he0⟩
    have hA_nonempty : ∀ i : Fin k, (A i).Nonempty := by
      intro i; exact ⟨e0 i, hH e0 he0 i⟩
    set P : ENNReal := wz1VertexCardProduct A Finset.univ with hP_def
    have hP_pos : 0 < P := by
      rw [hP_def, wz1VertexCardProduct]
      have h_nat : 0 < ∏ i ∈ (Finset.univ : Finset (Fin k)), (A i).card :=
        Finset.prod_pos (fun i _ => Finset.card_pos.mpr (hA_nonempty i))
      exact_mod_cast h_nat
    have hP_ne_zero : P ≠ 0 := hP_pos.ne'
    have hP_ne_top : P ≠ ⊤ := by
      rw [hP_def, wz1VertexCardProduct]
      apply ENNReal.prod_ne_top
      intro i _
      exact ENNReal.coe_ne_top
    set c : ENNReal := (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) / P with hc_def
    have hc_ne_top : c ≠ ⊤ := threshold_finite hε_lt_one H.card P hP_pos
    set T : Finset (Fin k) → ENNReal := fun I =>
      c * wz1VertexCardProduct A (Finset.univ \ I) with hT_def
    have hT_ne_top : ∀ I, T I ≠ ⊤ := by
      intro I
      simp only [hT_def]
      have h4 : c ≠ ⊤ := hc_ne_top
      have h5 : wz1VertexCardProduct A (Finset.univ \ I) ≠ ⊤ := by
        rw [wz1VertexCardProduct]
        apply ENNReal.prod_ne_top
        intro j _
        exact ENNReal.coe_ne_top
      exact ENNReal.mul_ne_top h4 h5
    let Φ (S : Finset (Fin k → α)) : ENNReal :=
      ∑ I : Finset (Fin k), (S.image (wz1Restrict I)).card * T I
    let IsDense (S : Finset (Fin k → α)) : Prop :=
      ∀ e ∈ S, ∀ I : Finset (Fin k),
        T I ≤ ((wz1HypergraphFiber S I e).card : ENNReal)

    have h_potential_decrease : ∀ (S : Finset (Fin k → α)) (e : Fin k → α)
        (he : e ∈ S) (I : Finset (Fin k)),
        Φ (S \ wz1HypergraphFiber S I e) + T I ≤ Φ S := by
      intro S e he I
      let F := wz1HypergraphFiber S I e
      let S₁ := S \ F
      let card₀ : Finset (Fin k) → ℕ := fun J => (S.image (wz1Restrict J)).card
      let card₁ : Finset (Fin k) → ℕ := fun J => (S₁.image (wz1Restrict J)).card
      have h_raw : card₁ I = card₀ I - 1 := by
        simpa [card₀, card₁, S₁, F] using fiber_deletion_count_eq S I e he
      have h_pos : 0 < card₀ I := by
        have h_in : wz1Restrict I e ∈ S.image (wz1Restrict I) :=
          Finset.mem_image.mpr ⟨e, he, rfl⟩
        exact Finset.card_pos.mpr ⟨wz1Restrict I e, h_in⟩
      have h_eq : card₀ I = card₁ I + 1 := by
        rw [h_raw]
        exact (Nat.sub_add_cancel h_pos).symm
      have h_mono : ∀ J ≠ I, card₁ J ≤ card₀ J := by
        intro J _
        exact fiber_deletion_count_le S I J e
      exact potential_decrease card₀ card₁ T I h_eq h_mono (hT_ne_top I)

    have h_potential_bound : Φ H ≤ epsilon * (H.card : ENNReal) := by
      have h1 : ∀ (I : Finset (Fin k)),
          (H.image (wz1Restrict I)).card * T I ≤
          (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) := by
        intro I
        have h_card2 : (H.image (wz1Restrict I)).card ≤ ∏ i ∈ I, (A i).card :=
          restrict_count_le A H hH H (by rfl) I
        have h7 : wz1VertexCardProduct A I = ∏ i ∈ I, (A i).card := by
          simp [wz1VertexCardProduct]
        have h6 : ((H.image (wz1Restrict I)).card : ENNReal) ≤ wz1VertexCardProduct A I := by
          rw [h7]
          exact_mod_cast h_card2
        have h_main : (H.image (wz1Restrict I)).card * T I ≤ wz1VertexCardProduct A I * T I :=
          mul_le_mul_of_nonneg_right h6 (by simp)
        have h_part : wz1VertexCardProduct A I * T I = c * P := by
          have hT : T I = c * wz1VertexCardProduct A (Finset.univ \ I) := by rfl
          rw [hT]
          have h : wz1VertexCardProduct A I * (c * wz1VertexCardProduct A (Finset.univ \ I)) =
              c * (wz1VertexCardProduct A I * wz1VertexCardProduct A (Finset.univ \ I)) := by
            ring
          rw [h, product_split A I]
        have h_cP : c * P = (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) := by
          have hc : c = (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) / P := by rfl
          rw [hc]
          rw [ENNReal.div_mul_cancel hP_ne_zero hP_ne_top]
        rw [h_part, h_cP] at h_main
        exact h_main
      have h_card_univ : (Finset.univ : Finset (Finset (Fin k))).card = 2 ^ k := by
        simp [Fintype.card_finset] <;> omega
      have hε_ne_top : epsilon ≠ ⊤ := by
        intro htop
        rw [htop] at hε_lt_one
        simp at hε_lt_one
      calc
        Φ H
          = ∑ I : Finset (Fin k), (H.image (wz1Restrict I)).card * T I := rfl
        _ ≤ ∑ I : Finset (Fin k), (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) := by
          apply Finset.sum_le_sum; intro I _; exact h1 I
        _ = (Finset.univ.card : ENNReal) * ((epsilon / (2 : ENNReal)^k) * (H.card : ENNReal)) := by
          let x : ENNReal := (epsilon / (2 : ENNReal)^k) * (H.card : ENNReal)
          have h_nsmul : ∀ (n : ℕ) (y : ENNReal), n • y = (n : ENNReal) * y := by
            intro n y
            induction n with
            | zero => simp
            | succ n ih =>
              rw [succ_nsmul, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
              <;> rfl
          have h : ∑ I : Finset (Fin k), x = (Finset.univ.card) • x := Finset.sum_const x
          rw [h]
          exact h_nsmul (Finset.univ.card) x
        _ = epsilon * (H.card : ENNReal) := by
          let univ' := (Finset.univ : Finset (Finset (Fin k)))
          have h_cast : (univ'.card : ENNReal) = (2 ^ k : ENNReal) := by
            exact_mod_cast h_card_univ
          rw [h_cast]
          have h2k_ne_zero : (2 ^ k : ENNReal) ≠ 0 := by positivity
          have h2k_ne_top : (2 ^ k : ENNReal) ≠ ⊤ := by
            exact_mod_cast ENNReal.natCast_ne_top (2 ^ k)
          have h : (2 ^ k : ENNReal) * (epsilon / (2 ^ k : ENNReal)) = epsilon :=
            ENNReal.mul_div_cancel h2k_ne_zero h2k_ne_top
          rw [← mul_assoc, h]

    have h_main : ∀ (S : Finset (Fin k → α)), S ⊆ H →
        ∃ (H' : Finset (Fin k → α)), H' ⊆ S ∧ IsDense H' ∧
          Φ H' + ((S \ H').card : ENNReal) ≤ Φ S := by
      apply Finset.strongInduction
      intro S ih
      intro hS_sub_H
      by_cases hDense : (∀ e ∈ S, ∀ I : Finset (Fin k), T I ≤ ((wz1HypergraphFiber S I e).card : ENNReal))
      · exact ⟨S, by rfl, hDense, by simp⟩
      · have h_main_goal : ∃ (e : Fin k → α), e ∈ S ∧ ∃ (I : Finset (Fin k)),
            ((wz1HypergraphFiber S I e).card : ENNReal) < T I :=
          not_dense_to_exists S T hDense
        rcases h_main_goal with ⟨e1, he1S, I1, hF1_small⟩
        let F := wz1HypergraphFiber S I1 e1
        have heF : e1 ∈ F := by
          dsimp only [F, wz1HypergraphFiber]
          rw [Finset.mem_filter]
          exact ⟨he1S, by simp⟩
        have hF_nonempty : F.Nonempty := ⟨e1, heF⟩
        let S₁ := S \ F
        have hF_sub_S : F ⊆ S := by
          dsimp only [F, wz1HypergraphFiber]
          exact Finset.filter_subset _ _
        have hS₁_card_lt : S₁.card < S.card := by
          rw [Finset.card_sdiff_of_subset hF_sub_S]
          exact Nat.sub_lt_self (Finset.card_pos.mpr hF_nonempty) (Finset.card_le_card hF_sub_S)
        have hS₁_sub_S : S₁ ⊆ S := by
          intro x hx
          exact (Finset.mem_sdiff.mp hx).1
        have hS₁_ssub_S : S₁ ⊂ S := by
          refine' ⟨hS₁_sub_S, _⟩
          intro h_sup
          have h_eq : S = S₁ := Finset.Subset.antisymm h_sup hS₁_sub_S
          have h_eq_card : S.card = S₁.card := by rw [h_eq]
          rw [h_eq_card] at hS₁_card_lt
          exact lt_irrefl _ hS₁_card_lt
        have hS₁_sub_H : S₁ ⊆ H := hS₁_sub_S.trans hS_sub_H
        rcases ih S₁ hS₁_ssub_S hS₁_sub_H with ⟨H', hH'_sub_S₁, hH'_dense, h_ih⟩
        have hH'_sub_S : H' ⊆ S := hH'_sub_S₁.trans hS₁_sub_S
        have hH'_disj_F : Disjoint H' F := by
          rw [Finset.disjoint_left]
          intro x hxH' hxF
          have hxS₁ : x ∈ S₁ := hH'_sub_S₁ hxH'
          exact (Finset.mem_sdiff.mp hxS₁).2 hxF
        have h_union : (S \ H') = (S₁ \ H') ∪ F := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxS, hxnH'⟩
            by_cases hxF : x ∈ F
            · exact Or.inr hxF
            · have hxS1 : x ∈ S₁ := Finset.mem_sdiff.mpr ⟨hxS, hxF⟩
              exact Or.inl ⟨hxS1, hxnH'⟩
          · rintro (h | hxF2)
            · have hxS : x ∈ S := hS₁_sub_S h.1
              exact ⟨hxS, h.2⟩
            · have hxS : x ∈ S := hF_sub_S hxF2
              have hxnH' : x ∉ H' := by
                intro h2
                exact Finset.disjoint_left.mp hH'_disj_F h2 hxF2
              exact ⟨hxS, hxnH'⟩
        have h_disj2 : Disjoint (S₁ \ H') F := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h : x ∈ S₁ := (Finset.mem_sdiff.mp hx1).1
          exact (Finset.mem_sdiff.mp h).2 hx2
        have h_card : (S \ H').card = (S₁ \ H').card + F.card := by
          rw [h_union, Finset.card_union_of_disjoint h_disj2]
        have hPhiS1_ne_top : Φ S₁ ≠ ⊤ := by
          have h : ∀ (I : Finset (Fin k)), (S₁.image (wz1Restrict I)).card * T I ≠ ⊤ :=
            fun I => ENNReal.mul_ne_top ENNReal.coe_ne_top (hT_ne_top I)
          have h' : (∑ I : Finset (Fin k), (S₁.image (wz1Restrict I)).card * T I) ≠ ⊤ :=
            (ENNReal.sum_ne_top).mpr (fun I _ => h I)
          simpa [Φ] using h'
        refine' ⟨H', hH'_sub_S, hH'_dense, _⟩
        have h4 : Φ H' + ((S \ H').card : ENNReal) =
            Φ H' + ((S₁ \ H').card : ENNReal) + (F.card : ENNReal) := by
          rw [h_card, Nat.cast_add] <;> abel
        rw [h4]
        have h5 : Φ H' + ((S₁ \ H').card : ENNReal) ≤ Φ S₁ := h_ih
        have h6 : Φ S₁ + (F.card : ENNReal) ≤ Φ S := by
          have h7 : Φ S₁ + T I1 ≤ Φ S := h_potential_decrease S e1 he1S I1
          have h8 : (F.card : ENNReal) < T I1 := hF1_small
          have h9 : Φ S₁ + (F.card : ENNReal) < Φ S₁ + T I1 :=
            ENNReal.add_lt_add_left hPhiS1_ne_top h8
          exact h9.le.trans h7
        have h10 : Φ H' + ((S₁ \ H').card : ENNReal) + (F.card : ENNReal) ≤
            Φ S₁ + (F.card : ENNReal) := by
          gcongr
        exact h10.trans h6

    rcases h_main H (by rfl) with ⟨H', hH'_sub_H, hH'_dense, h_ih⟩
    have h_removed_bound : ((H \ H').card : ENNReal) ≤ epsilon * (H.card : ENNReal) := by
      have h : Φ H' + ((H \ H').card : ENNReal) ≤ Φ H := h_ih
      have h1 : ((H \ H').card : ENNReal) ≤ Φ H' + ((H \ H').card : ENNReal) := by simp
      exact h1.trans h |>.trans h_potential_bound
    have h_sum_cards : (H'.card : ENNReal) + ((H \ H').card : ENNReal) = (H.card : ENNReal) := by
      have h2 : (H \ H') ∪ H' = H := by
        ext x
        simp [hH'_sub_H]
        <;> tauto
      have h3 : Disjoint (H \ H') H' := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx1).2 hx2
      have h4 : ((H \ H') ∪ H').card = (H \ H').card + H'.card := Finset.card_union_of_disjoint h3
      have h5 : (H \ H').card + H'.card = H.card := by
        rw [←h4, h2]
      have h' : (H'.card : ENNReal) + ((H \ H').card : ENNReal) = (H.card : ENNReal) := by
        rw [add_comm]
        exact_mod_cast h5
      exact h'
    have hε_sum : (1 - epsilon) + epsilon = (1 : ENNReal) :=
      tsub_add_cancel_iff_le.mpr hε_lt_one.le
    have h_retention : (1 - epsilon) * (H.card : ENNReal) ≤ (H'.card : ENNReal) := by
      have h : (1 - epsilon) * (H.card : ENNReal) + ((H \ H').card : ENNReal) ≤
          (H.card : ENNReal) := by
        calc
          (1 - epsilon) * (H.card : ENNReal) + ((H \ H').card : ENNReal)
            ≤ (1 - epsilon) * (H.card : ENNReal) + epsilon * (H.card : ENNReal) :=
              add_le_add_right h_removed_bound ((1 - epsilon) * (H.card : ENNReal))
          _ = ((1 - epsilon) + epsilon) * (H.card : ENNReal) := by rw [add_mul]
          _ = (1 : ENNReal) * (H.card : ENNReal) := by rw [hε_sum]
          _ = (H.card : ENNReal) := by simp
      have h' : (1 - epsilon) * (H.card : ENNReal) + ((H \ H').card : ENNReal) ≤
          (H'.card : ENNReal) + ((H \ H').card : ENNReal) := by
        rw [h_sum_cards] <;> exact h
      have h_top : ((H \ H').card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      exact (ENNReal.add_le_add_iff_right h_top).mp h'
    have h_support : ∀ edge ∈ H', ∀ i, edge i ∈ A i := by
      intro edge hedge i
      exact hH edge (hH'_sub_H hedge) i
    have hc' : c = (epsilon / (2 : ENNReal)^k) * ((H.card : ENNReal) / P) := by
      simp only [hc_def]
      have h : ((epsilon / (2 : ENNReal)^k) * (H.card : ENNReal) / P) =
          (epsilon / (2 : ENNReal)^k) * ((H.card : ENNReal) / P) := by
        simp only [div_eq_mul_inv, mul_assoc]
      rw [h]
    have h_density : ∀ edge ∈ H', ∀ I : Finset (Fin k),
        (epsilon / (2 : ENNReal)^k) * ((H.card : ENNReal) / P) * wz1VertexCardProduct A (Finset.univ \ I) ≤
          ((wz1HypergraphFiber H' I edge).card : ENNReal) := by
      intro edge hedge I
      simpa [hT_def, hc'] using hH'_dense edge hedge I
    exact ⟨H', hH'_sub_H, h_retention, ⟨h_support, h_density⟩⟩

end Kakeya.Assouad
