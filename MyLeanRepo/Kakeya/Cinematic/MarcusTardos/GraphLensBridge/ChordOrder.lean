import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.Fibers

/-!
# The six-point chord-order lemma

Marcus--Tardos Lemma 10 reduces the intersection-reverse claim to a finite
order fact about two cyclic triples.  Among the three matched pairs, either
the two host chords or the two symbol chords alternate.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge


/-- Positive cyclic order inherited from a linear order. -/
def CyclicLT {α : Type*} [LT α] (x y z : α) : Prop :=
  (x < y ∧ y < z) ∨ (y < z ∧ z < x) ∨ (z < x ∧ x < y)

/-- The endpoints of two chords alternate in the linearized circle. -/
def Alternates {α : Type*} [LT α] (x₁ y₁ x₂ y₂ : α) : Prop :=
  (x₁ < x₂ ∧ x₂ < y₁ ∧ y₁ < y₂) ∨
  (x₂ < y₁ ∧ y₁ < y₂ ∧ y₂ < x₁) ∨
  (y₁ < y₂ ∧ y₂ < x₁ ∧ x₁ < x₂) ∨
  (y₂ < x₁ ∧ x₁ < x₂ ∧ x₂ < y₁) ∨
  (x₁ < y₂ ∧ y₂ < y₁ ∧ y₁ < x₂) ∨
  (y₂ < y₁ ∧ y₁ < x₂ ∧ x₂ < x₁) ∨
  (y₁ < x₂ ∧ x₂ < x₁ ∧ x₁ < y₂) ∨
  (x₂ < x₁ ∧ x₁ < y₂ ∧ y₂ < y₁)

def BadPair {α : Type*} [LT α] (ai aj bi bj : α) : Prop :=
  Alternates ai aj bi bj ∨ Alternates ai bi aj bj

private instance (x y z : Fin 6) : Decidable (CyclicLT x y z) := by
  unfold CyclicLT
  infer_instance

private instance (x₁ y₁ x₂ y₂ : Fin 6) : Decidable (Alternates x₁ y₁ x₂ y₂) := by
  unfold Alternates
  infer_instance

private instance (ai aj bi bj : Fin 6) : Decidable (BadPair ai aj bi bj) := by
  unfold BadPair
  infer_instance

private theorem fin_chord_decision :
    ∀ (ap aa ab bp ba bb : Fin 6),
      List.Pairwise (fun x y => x ≠ y) [ap, aa, ab, bp, ba, bb] →
      CyclicLT ap aa ab → CyclicLT bp ba bb →
      BadPair ap aa bp ba ∨
        BadPair ap ab bp bb ∨ BadPair aa ab ba bb := by
  decide

private theorem fin_chord
    (ap aa ab bp ba bb : Fin 6)
    (hdistinct :
      List.Pairwise (fun x y => x ≠ y) [ap, aa, ab, bp, ba, bb])
    (hA : CyclicLT ap aa ab) (hB : CyclicLT bp ba bb) :
    BadPair ap aa bp ba ∨
      BadPair ap ab bp bb ∨ BadPair aa ab ba bb :=
  fin_chord_decision ap aa ab bp ba bb hdistinct hA hB

theorem chord_order
    {ap aa ab bp ba bb : ℝ}
    (hdistinct :
      List.Pairwise (fun x y : ℝ => x ≠ y) [ap, aa, ab, bp, ba, bb])
    (hA : CyclicLT ap aa ab) (hB : CyclicLT bp ba bb) :
    BadPair ap aa bp ba ∨
      BadPair ap ab bp bb ∨ BadPair aa ab ba bb := by
  classical
  let points : Finset ℝ := {ap, aa, ab, bp, ba, bb}
  have hcard : points.card = 6 := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at hdistinct
    simp_all [points]
  let order : Fin 6 ≃o points := points.orderIsoOfFin hcard
  let rank (x : ℝ) (hx : x ∈ points) : Fin 6 :=
    order.symm ⟨x, hx⟩
  have hap : ap ∈ points := by simp [points]
  have haa : aa ∈ points := by simp [points]
  have hab : ab ∈ points := by simp [points]
  have hbp : bp ∈ points := by simp [points]
  have hba : ba ∈ points := by simp [points]
  have hbb : bb ∈ points := by simp [points]
  let rap := rank ap hap
  let raa := rank aa haa
  let rab := rank ab hab
  let rbp := rank bp hbp
  let rba := rank ba hba
  let rbb := rank bb hbb
  have hrank_injective :
      ∀ {x y : ℝ} (hx : x ∈ points) (hy : y ∈ points),
        rank x hx = rank y hy → x = y := by
    intro x y hx hy hxy
    have := congrArg order hxy
    simpa [rank] using congrArg Subtype.val this
  have hfinDistinct :
      List.Pairwise (fun x y => x ≠ y) [rap, raa, rab, rbp, rba, rbb] := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at hdistinct
    constructor
    · exact ⟨
        fun h => hdistinct.1.1 (hrank_injective hap haa h),
        fun h => hdistinct.1.2.1 (hrank_injective hap hab h),
        fun h => hdistinct.1.2.2.1 (hrank_injective hap hbp h),
        fun h => hdistinct.1.2.2.2.1 (hrank_injective hap hba h),
        fun h => hdistinct.1.2.2.2.2 (hrank_injective hap hbb h)⟩
    · constructor
      · exact ⟨
          fun h => hdistinct.2.1.1 (hrank_injective haa hab h),
          fun h => hdistinct.2.1.2.1 (hrank_injective haa hbp h),
          fun h => hdistinct.2.1.2.2.1 (hrank_injective haa hba h),
          fun h => hdistinct.2.1.2.2.2 (hrank_injective haa hbb h)⟩
      · constructor
        · exact ⟨
            fun h => hdistinct.2.2.1.1 (hrank_injective hab hbp h),
            fun h => hdistinct.2.2.1.2.1 (hrank_injective hab hba h),
            fun h => hdistinct.2.2.1.2.2 (hrank_injective hab hbb h)⟩
        · constructor
          · exact ⟨
              fun h => hdistinct.2.2.2.1.1 (hrank_injective hbp hba h),
              fun h => hdistinct.2.2.2.1.2 (hrank_injective hbp hbb h)⟩
          · constructor
            · exact fun h =>
                hdistinct.2.2.2.2.1 (hrank_injective hba hbb h)
            · exact ⟨fun _ h => h.elim, List.Pairwise.nil⟩
  have rank_lt_iff {x y : ℝ} (hx : x ∈ points) (hy : y ∈ points) :
      rank x hx < rank y hy ↔ x < y := by
    change order.symm ⟨x, hx⟩ < order.symm ⟨y, hy⟩ ↔ x < y
    simpa using order.symm.lt_iff_lt
  have hfinA : CyclicLT rap raa rab := by
    simpa [CyclicLT, rap, raa, rab, rank_lt_iff] using hA
  have hfinB : CyclicLT rbp rba rbb := by
    simpa [CyclicLT, rbp, rba, rbb, rank_lt_iff] using hB
  have hfin := fin_chord rap raa rab rbp rba rbb
    hfinDistinct hfinA hfinB
  simpa [BadPair, Alternates, rap, raa, rab, rbp, rba, rbb,
    rank_lt_iff] using hfin

end Kakeya.Cinematic.GraphLensBridge
