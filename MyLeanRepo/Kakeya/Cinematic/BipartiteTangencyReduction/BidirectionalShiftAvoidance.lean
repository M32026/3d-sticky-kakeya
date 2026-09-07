import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.BidirectionalShiftAvoidanceInputs

/-!
# Preserve no exact tangencies in both shift directions
-/

namespace Kakeya.Cinematic

open MeasureTheory

theorem bidirectional_shift_avoidance :
    BidirectionalShiftAvoidanceStatement := by
  classical
  intro W B F I shift0 hF h_base epsilonLow epsilonHigh h_eps
  let badUp : Set ℝ := {epsilon | ∃ p ∈ (W.toFinset ×ˢ B.toFinset),
    (shift0 p.1 - shift0 p.2) + epsilon ∈ badSet p.1 p.2 I}
  let badDown : Set ℝ := {epsilon | ∃ p ∈ (W.toFinset ×ˢ B.toFinset),
    (shift0 p.1 - shift0 p.2) - epsilon ∈ badSet p.1 p.2 I}
  have h_up_null : volume badUp = 0 := badUnion_up_measure_zero shift0
  have h_down_null : volume badDown = 0 := badUnion_down_measure_zero shift0
  have h_union_null : volume (badUp ∪ badDown) = 0 :=
    measure_union_null h_up_null h_down_null
  rcases exists_real_notin_null_set h_eps h_union_null with
    ⟨epsilon, h_eps_low, h_eps_high, h_notin_union⟩
  have h_notin_up : epsilon ∉ badUp := by
    intro h
    exact h_notin_union (Or.inl h)
  have h_notin_down : epsilon ∉ badDown := by
    intro h
    exact h_notin_union (Or.inr h)
  refine ⟨epsilon, h_eps_low, h_eps_high, ?_⟩
  dsimp only
  set shiftUp : C2Function → ℝ := fun f =>
    if f ∈ W.toFinset then epsilon + shift0 f else shift0 f with hshiftUp
  set shiftDown : C2Function → ℝ := fun f =>
    if f ∈ W.toFinset then -epsilon + shift0 f else shift0 f with hshiftDown
  have hW : (W.toFinset : Set C2Function) = W.carrier :=
    W.finite.coe_toFinset
  have hB : (B.toFinset : Set C2Function) = B.carrier :=
    B.finite.coe_toFinset
  have h_base' : ∀ (f : C2Function), f ∈ F.carrier →
      ∀ (g : C2Function), g ∈ F.carrier → f ≠ g →
        shift0 f - shift0 g ∉ badSet f g I := by
    intro f hf g hg hne
    exact (tangency_iff_notin_badSet f g I shift0).mp
      (h_base hf hg hne)
  have h_in_F_imp : ∀ (f : C2Function), f ∈ F.carrier →
      (f ∈ W.toFinset ∨ f ∈ B.toFinset) := by
    intro f hf
    have h : f ∈ W.carrier ∪ B.carrier := by
      rw [← hF]
      exact hf
    rcases h with h | h
    · left
      have h2 : f ∈ (W.toFinset : Set C2Function) := by
        rw [hW]
        exact h
      exact h2
    · right
      have h2 : f ∈ (B.toFinset : Set C2Function) := by
        rw [hB]
        exact h
      exact h2
  have hUp_pos : ∀ (x : C2Function), x ∈ W.toFinset →
      shiftUp x = epsilon + shift0 x := by
    intro x hx
    have h :
        shiftUp x =
          (if x ∈ W.toFinset then epsilon + shift0 x else shift0 x) :=
      congrFun hshiftUp x
    rw [h, if_pos hx]
  have hUp_neg : ∀ (x : C2Function), x ∉ W.toFinset →
      shiftUp x = shift0 x := by
    intro x hx
    have h :
        shiftUp x =
          (if x ∈ W.toFinset then epsilon + shift0 x else shift0 x) :=
      congrFun hshiftUp x
    rw [h, if_neg hx]
  have hDown_pos : ∀ (x : C2Function), x ∈ W.toFinset →
      shiftDown x = -epsilon + shift0 x := by
    intro x hx
    have h :
        shiftDown x =
          (if x ∈ W.toFinset then -epsilon + shift0 x else shift0 x) :=
      congrFun hshiftDown x
    rw [h, if_pos hx]
  have hDown_neg : ∀ (x : C2Function), x ∉ W.toFinset →
      shiftDown x = shift0 x := by
    intro x hx
    have h :
        shiftDown x =
          (if x ∈ W.toFinset then -epsilon + shift0 x else shift0 x) :=
      congrFun hshiftDown x
    rw [h, if_neg hx]
  have h_getB : ∀ (x : C2Function), x ∈ F.carrier →
      x ∉ W.toFinset → x ∈ B.toFinset := by
    intro x hx hnx
    rcases h_in_F_imp x hx with h' | h'
    · exact (hnx h').elim
    · exact h'
  have h_up_main : ∀ (f : C2Function), f ∈ F.carrier →
      ∀ (g : C2Function), g ∈ F.carrier → f ≠ g →
        shiftUp f - shiftUp g ∉ badSet f g I := by
    intro f hf g hg hne
    by_cases hfW : f ∈ W.toFinset
    · by_cases hgW : g ∈ W.toFinset
      · rw [hUp_pos f hfW, hUp_pos g hgW]
        have h_eq :
            (epsilon + shift0 f) - (epsilon + shift0 g) =
              shift0 f - shift0 g := by
          ring
        rw [h_eq]
        exact h_base' f hf g hg hne
      · have hgB : g ∈ B.toFinset := h_getB g hg hgW
        rw [hUp_pos f hfW, hUp_neg g hgW]
        have h_eq :
            (epsilon + shift0 f) - shift0 g =
              (shift0 f - shift0 g) + epsilon := by
          ring
        rw [h_eq]
        intro h_contra
        have h4 : (f, g) ∈ W.toFinset ×ˢ B.toFinset :=
          Finset.mem_product.mpr ⟨hfW, hgB⟩
        exact h_notin_up ⟨(f, g), h4, h_contra⟩
    · have hfB : f ∈ B.toFinset := h_getB f hf hfW
      by_cases hgW : g ∈ W.toFinset
      · rw [hUp_neg f hfW, hUp_pos g hgW]
        have h_eq :
            shift0 f - (epsilon + shift0 g) =
              (shift0 f - shift0 g) - epsilon := by
          ring
        rw [h_eq]
        intro h_contra
        have h_symm :
            badSet g f I = Neg.neg '' (badSet f g I) :=
          badSet_symm f g I
        have h6 :
            (shift0 g - shift0 f) + epsilon ∈ badSet g f I := by
          rw [h_symm]
          refine ⟨(shift0 f - shift0 g) - epsilon, h_contra, ?_⟩
          ring
        have h4 : (g, f) ∈ W.toFinset ×ˢ B.toFinset :=
          Finset.mem_product.mpr ⟨hgW, hfB⟩
        exact h_notin_up ⟨(g, f), h4, h6⟩
      · rw [hUp_neg f hfW, hUp_neg g hgW]
        exact h_base' f hf g hg hne
  have h_down_main : ∀ (f : C2Function), f ∈ F.carrier →
      ∀ (g : C2Function), g ∈ F.carrier → f ≠ g →
        shiftDown f - shiftDown g ∉ badSet f g I := by
    intro f hf g hg hne
    by_cases hfW : f ∈ W.toFinset
    · by_cases hgW : g ∈ W.toFinset
      · rw [hDown_pos f hfW, hDown_pos g hgW]
        have h_eq :
            (-epsilon + shift0 f) - (-epsilon + shift0 g) =
              shift0 f - shift0 g := by
          ring
        rw [h_eq]
        exact h_base' f hf g hg hne
      · have hgB : g ∈ B.toFinset := h_getB g hg hgW
        rw [hDown_pos f hfW, hDown_neg g hgW]
        have h_eq :
            (-epsilon + shift0 f) - shift0 g =
              (shift0 f - shift0 g) - epsilon := by
          ring
        rw [h_eq]
        intro h_contra
        have h4 : (f, g) ∈ W.toFinset ×ˢ B.toFinset :=
          Finset.mem_product.mpr ⟨hfW, hgB⟩
        exact h_notin_down ⟨(f, g), h4, h_contra⟩
    · have hfB : f ∈ B.toFinset := h_getB f hf hfW
      by_cases hgW : g ∈ W.toFinset
      · rw [hDown_neg f hfW, hDown_pos g hgW]
        have h_eq :
            shift0 f - (-epsilon + shift0 g) =
              (shift0 f - shift0 g) + epsilon := by
          ring
        rw [h_eq]
        intro h_contra
        have h_symm :
            badSet g f I = Neg.neg '' (badSet f g I) :=
          badSet_symm f g I
        have h6 :
            (shift0 g - shift0 f) - epsilon ∈ badSet g f I := by
          rw [h_symm]
          refine ⟨(shift0 f - shift0 g) + epsilon, h_contra, ?_⟩
          ring
        have h4 : (g, f) ∈ W.toFinset ×ˢ B.toFinset :=
          Finset.mem_product.mpr ⟨hgW, hfB⟩
        exact h_notin_down ⟨(g, f), h4, h6⟩
      · rw [hDown_neg f hfW, hDown_neg g hgW]
        exact h_base' f hf g hg hne
  have h_up_result : F.HasNoExactTangenciesOn I shiftUp := by
    dsimp only [FiniteFunctionFamily.HasNoExactTangenciesOn]
    intro f hf g hg hne
    exact (tangency_iff_notin_badSet f g I shiftUp).mpr
      (h_up_main f hf g hg hne)
  have h_down_result : F.HasNoExactTangenciesOn I shiftDown := by
    dsimp only [FiniteFunctionFamily.HasNoExactTangenciesOn]
    intro f hf g hg hne
    exact (tangency_iff_notin_badSet f g I shiftDown).mpr
      (h_down_main f hf g hg hne)
  exact ⟨h_up_result, h_down_result⟩

end Kakeya.Cinematic
