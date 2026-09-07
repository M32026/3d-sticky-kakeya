import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterProjectionFiberStatement

/-!
# Three-parameter projection fiber bound

This closes the indexed finite-fiber estimate used when the Section 7
cinematic reduction forgets the fourth tube parameter.
-/

namespace Kakeya.Assouad

theorem tube_parameter_projection_fiber_bound :
    TubeParameterProjectionFiberBoundStatement := by
  intro delta F C hFrost w hw_delta hw_one active c0 hwindow
  let B : ENNReal := C * Kakeya.realRpowENN w 2 * F.enncard
  let f : Fin F.card → Point 3 := tubeParameterPoint3
  let img : Finset (Point 3) := active.image f
  have h_fiber_bound : ∀ p ∈ img,
      ((active.filter fun i => f i = p).card : ENNReal) ≤ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i0, hi0, rfl⟩
    let fiber := active.filter fun i => f i = f i0
    have h1 : ∀ i ∈ fiber,
        |(tubeParams i).a - (tubeParams i0).a| ≤ w ∧
        |(tubeParams i).b - (tubeParams i0).b| ≤ w ∧
        |(tubeParams i).c - (tubeParams i0).c| ≤ w ∧
        |(tubeParams i).d - (tubeParams i0).d| ≤ w := by
      intro i hi
      have h_i_active : i ∈ active := (Finset.mem_filter.mp hi).1
      have h_eq : f i = f i0 := (Finset.mem_filter.mp hi).2
      have ha : (tubeParams i).a = (tubeParams i0).a := by
        have h : (f i) 0 = (f i0) 0 := by rw [h_eq]
        have h' : (tubeParams i).a / 24 = (tubeParams i0).a / 24 := by
          simpa [f, tubeParameterPoint3, point3] using h
        linarith
      have hb : (tubeParams i).b = (tubeParams i0).b := by
        have h : (f i) 1 = (f i0) 1 := by rw [h_eq]
        have h' : (tubeParams i).b / 24 = (tubeParams i0).b / 24 := by
          simpa [f, tubeParameterPoint3, point3] using h
        linarith
      have hd : (tubeParams i).d = (tubeParams i0).d := by
        have h : (f i) 2 = (f i0) 2 := by rw [h_eq]
        have h' : (tubeParams i).d / 4 = (tubeParams i0).d / 4 := by
          simpa [f, tubeParameterPoint3, point3] using h
        linarith
      have hw_nonneg : 0 ≤ w := by
        have h : 0 ≤ |(tubeParams i0).c - c0| := abs_nonneg _
        have h' : |(tubeParams i0).c - c0| ≤ w / 2 := hwindow i0 hi0
        linarith
      have hc : |(tubeParams i).c - (tubeParams i0).c| ≤ w := by
        have h_i : |(tubeParams i).c - c0| ≤ w / 2 := hwindow i h_i_active
        have h_i0 : |(tubeParams i0).c - c0| ≤ w / 2 := hwindow i0 hi0
        have h_tri : |(tubeParams i).c - (tubeParams i0).c| ≤
            |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| :=
          abs_sub_le (tubeParams i).c c0 (tubeParams i0).c
        rw [show |c0 - (tubeParams i0).c| = |(tubeParams i0).c - c0| by
          rw [abs_sub_comm]] at h_tri
        linarith
      exact ⟨by rw [ha]; simp [hw_nonneg], by rw [hb]; simp [hw_nonneg], hc,
        by rw [hd]; simp [hw_nonneg]⟩
    let frostSet := Finset.univ.filter fun i : Fin F.card =>
      |(tubeParams i).a - (tubeParams i0).a| ≤ w ∧
      |(tubeParams i).b - (tubeParams i0).b| ≤ w ∧
      |(tubeParams i).c - (tubeParams i0).c| ≤ w ∧
      |(tubeParams i).d - (tubeParams i0).d| ≤ w
    have h_subset : fiber ⊆ frostSet := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1 i hi⟩
    have h2 : (fiber.card : ENNReal) ≤ (frostSet.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h_subset
    have h3 : (frostSet.card : ENNReal) ≤ B := hFrost w hw_delta hw_one i0
    exact le_trans h2 h3
  let fiber : Point 3 → Finset (Fin F.card) := fun p =>
    active.filter fun i => f i = p
  have h_disj : Set.PairwiseDisjoint (img : Set (Point 3)) fiber := by
    intro p _ q _ hne
    simp only [Finset.disjoint_left]
    intro i hi1 hi2
    have h4 : f i = p := (Finset.mem_filter.mp hi1).2
    have h5 : f i = q := (Finset.mem_filter.mp hi2).2
    have h6 : p = q := by rw [←h4, h5]
    exact hne h6
  have h_bunion : img.biUnion fiber = active := by
    ext i
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter]
    constructor
    · rintro ⟨p, _, h_i_active, _⟩
      exact h_i_active
    · intro hi
      refine ⟨f i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hi, rfl⟩
  have h_card : active.card = ∑ p ∈ img, (fiber p).card := by
    rw [←h_bunion, Finset.card_biUnion h_disj]
  have h_enn : (active.card : ENNReal) = ∑ p ∈ img, ((fiber p).card : ENNReal) := by
    exact_mod_cast h_card
  have h_sum : ∑ p ∈ img, ((fiber p).card : ENNReal) ≤ ∑ p ∈ img, B := by
    apply Finset.sum_le_sum
    intro p hp
    exact h_fiber_bound p hp
  have h_sum_const : ∑ p ∈ img, B = B * (img.card : ENNReal) := by
    have h : ∑ p ∈ img, B = (img.card : ENNReal) * B := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    rw [h, mul_comm]
  have h_main2 : (active.card : ENNReal) ≤ B * (img.card : ENNReal) := by
    rw [h_enn]
    have h_sum' : ∑ p ∈ img, ((fiber p).card : ENNReal) ≤
        B * (img.card : ENNReal) := by
      rw [←h_sum_const]
      exact h_sum
    exact h_sum'
  exact ⟨h_fiber_bound, by
    have h_final : (active.card : ENNReal) ≤ B * (img.card : ENNReal) := h_main2
    simpa [img, B, mul_assoc, mul_comm, mul_left_comm] using h_final⟩

/--
Cancel the ambient indexed-family cardinality from an active-set lower bound
and the three-parameter fiber sum.

This is the no-injectivity replacement for the false equality between the
active indexed cardinality and the cardinality of its `(a,b,d)` image.
-/
theorem tube_parameter_projection_image_lower
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hF : F.Nonempty)
    (C : ENNReal)
    (hFrost : TubeParameterFrostmanBound F C)
    (w : ℝ) (hw_delta : delta ≤ w) (hw_one : w ≤ 1)
    (active : Finset (Fin F.card))
    (c0 : ℝ)
    (hwindow : ∀ i ∈ active, |(tubeParams i).c - c0| ≤ w / 2)
    (lambda : ENNReal)
    (hactive : lambda * F.enncard ≤ (active.card : ENNReal)) :
    lambda ≤
      (C * Kakeya.realRpowENN w 2) *
        ((active.image tubeParameterPoint3).card : ENNReal) := by
  have hsum :=
    (tube_parameter_projection_fiber_bound F C hFrost w hw_delta hw_one
      active c0 hwindow).2
  have hchain :
      lambda * F.enncard ≤
        ((C * Kakeya.realRpowENN w 2) *
          ((active.image tubeParameterPoint3).card : ENNReal)) *
            F.enncard := by
    calc
      lambda * F.enncard ≤ (active.card : ENNReal) := hactive
      _ ≤ (C * Kakeya.realRpowENN w 2 * F.enncard) *
          ((active.image tubeParameterPoint3).card : ENNReal) := hsum
      _ = ((C * Kakeya.realRpowENN w 2) *
          ((active.image tubeParameterPoint3).card : ENNReal)) *
            F.enncard := by
        ring
  have hcard_ne_zero : F.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hF.ne'
  have hcard_ne_top : F.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hchain' :
      F.enncard * lambda ≤
        F.enncard *
          ((C * Kakeya.realRpowENN w 2) *
            ((active.image tubeParameterPoint3).card : ENNReal)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hchain
  exact
    (ENNReal.mul_le_mul_iff_right hcard_ne_zero hcard_ne_top).mp hchain'

end Kakeya.Assouad
