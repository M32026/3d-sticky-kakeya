import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.Perturbation.CriticalImage
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Finite avoidance of exact tangencies

Given a finite family of C² functions and a controlled interval, arbitrarily
small vertical shifts eliminate all exact tangencies on the interval.
-/

namespace Kakeya.Cinematic

open MeasureTheory

/-- Differences of shifts that create an exact tangency for a pair of functions. -/
def badSet (f g : C2Function) (I : ParameterInterval) : Set ℝ :=
  {r : ℝ | ∃ (x : UnitPoint), x ∈ I.carrier ∧
    f.firstDeriv x = g.firstDeriv x ∧ r = g x - f x}

/-- The bad difference set has measure zero. -/
lemma badSet_measure_zero (f g : C2Function) (I : ParameterInterval) :
    volume (badSet f g I) = 0 := by
  let h : ℝ → ℝ := fun x => g.extension x - f.extension x
  have h_hdiff : ContDiff ℝ 2 h :=
    g.extension_contDiff.sub f.extension_contDiff
  let criticalSet : Set ℝ := {x ∈ Set.Icc I.left I.right | deriv h x = 0}
  have h_sard : volume (h '' criticalSet) = 0 :=
    critical_image_measure_zero h_hdiff I.left I.right I.left_le_right
  have h_deriv : ∀ (x : UnitPoint), deriv h (x : ℝ) = g.firstDeriv x - f.firstDeriv x := by
    intro x
    have h_g_diff : DifferentiableAt ℝ g.extension (x : ℝ) :=
      (ContDiff.differentiable (g.extension_contDiff) (by norm_num)).differentiableAt
    have h_f_diff : DifferentiableAt ℝ f.extension (x : ℝ) :=
      (ContDiff.differentiable (f.extension_contDiff) (by norm_num)).differentiableAt
    have h3 : deriv h (x : ℝ) = deriv g.extension (x : ℝ) - deriv f.extension (x : ℝ) :=
      deriv_sub h_g_diff h_f_diff
    rw [h3, g.deriv_extension_eq_firstDeriv x, f.deriv_extension_eq_firstDeriv x]
  have h_eq : badSet f g I = h '' criticalSet := by
    ext r
    simp only [badSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, hderiv, rfl⟩
      refine ⟨(x : ℝ), ?_, ?_⟩
      · simp only [criticalSet, Set.mem_setOf_eq]
        have h1 : I.left ≤ (x : ℝ) ∧ (x : ℝ) ≤ I.right := hx
        exact ⟨⟨h1.1, h1.2⟩, by rw [h_deriv x, hderiv] <;> ring⟩
      · have h4 : h (x : ℝ) = g x - f x := by
          dsimp only [h]
          rw [g.extension_eq_value x, f.extension_eq_value x]
        rw [h4]
    · rintro ⟨y, hy, rfl⟩
      have h1 : I.left ≤ y ∧ y ≤ I.right := hy.1
      have h2 : y ∈ unitInterval := by
        exact ⟨le_trans I.left_mem.1 h1.1, le_trans h1.2 I.right_mem.2⟩
      let x : UnitPoint := ⟨y, h2⟩
      have h3 : x ∈ I.carrier := by
        simpa [ParameterInterval.carrier] using h1
      have h4 : deriv h y = 0 := hy.2
      have h5 : f.firstDeriv x = g.firstDeriv x := by
        have h6 : deriv h y = g.firstDeriv x - f.firstDeriv x := h_deriv x
        have h7 : g.firstDeriv x - f.firstDeriv x = 0 := by rw [← h6, h4]
        linarith
      have h8 : h y = g x - f x := by
        dsimp only [h]
        rw [g.extension_eq_value x, f.extension_eq_value x]
      exact ⟨x, h3, h5, h8⟩
  rw [h_eq]
  exact h_sard

/-- Avoiding a pair's bad set is equivalent to eliminating its exact tangencies. -/
lemma tangency_iff_notin_badSet (f g : C2Function) (I : ParameterInterval)
    (shift : C2Function → ℝ) :
    (∀ x ∈ I.carrier,
      (f.verticalTranslate (shift f)) x ≠ (g.verticalTranslate (shift g)) x ∨
      (f.verticalTranslate (shift f)).firstDeriv x ≠
        (g.verticalTranslate (shift g)).firstDeriv x)
    ↔ shift f - shift g ∉ badSet f g I := by
  simp only [badSet, Set.mem_setOf_eq]
  constructor
  · intro h h_bad
    rcases h_bad with ⟨x, hx, hderiv, hval⟩
    have h1 : (f.verticalTranslate (shift f)) x =
        (g.verticalTranslate (shift g)) x := by
      simp [C2Function.verticalTranslate, hval] <;> linarith
    have h2 : (f.verticalTranslate (shift f)).firstDeriv x =
        (g.verticalTranslate (shift g)).firstDeriv x := by
      simp [C2Function.verticalTranslate, hderiv]
    have h3 := h x hx
    rcases h3 with (h3 | h3)
    · exact h3 h1
    · exact h3 h2
  · intro h x hx
    by_cases h4 : (f.verticalTranslate (shift f)).firstDeriv x ≠
        (g.verticalTranslate (shift g)).firstDeriv x
    · exact Or.inr h4
    · have h5 : (f.verticalTranslate (shift f)).firstDeriv x =
          (g.verticalTranslate (shift g)).firstDeriv x := by
        tauto
      have h6 : (f.verticalTranslate (shift f)) x ≠
          (g.verticalTranslate (shift g)) x := by
        intro h7
        have h8 : shift f - shift g = g x - f x := by
          simp [C2Function.verticalTranslate] at h7 <;> linarith
        have h9 : f.firstDeriv x = g.firstDeriv x := by
          simp [C2Function.verticalTranslate] at h5 <;> linarith
        exact h ⟨x, hx, h9, h8⟩
      exact Or.inl h6

/-- Arbitrarily small shifts eliminate exact tangencies in a finite family. -/
theorem finiteAvoidanceExactTangencies : FiniteTangencyPerturbationStatement := by
  intro K D _ _ family _ I _ F _ epsilon hepsilon
  classical
  let s : Finset C2Function := F.toFinset
  have h_s : (s : Set C2Function) = F.carrier := F.finite.coe_toFinset
  have h_main : ∃ (shift : C2Function → ℝ),
      (∀ f ∈ s, |shift f| ≤ epsilon) ∧
      (∀ f ∈ s, ∀ g ∈ s, f ≠ g →
        ∀ x ∈ I.carrier,
          (f.verticalTranslate (shift f)) x ≠
            (g.verticalTranslate (shift g)) x ∨
          (f.verticalTranslate (shift f)).firstDeriv x ≠
            (g.verticalTranslate (shift g)).firstDeriv x) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, by simp, by simp⟩
    | @insert f s hf ih =>
      rcases ih with ⟨shift', h_bound', h_tang'⟩
      let translate (a : ℝ) (t : Set ℝ) : Set ℝ := (fun x => a + x) '' t
      let badUnion : Set ℝ := ⋃ g ∈ s, translate (shift' g) (badSet f g I)
      have h_translate_meas : ∀ (a : ℝ) (t : Set ℝ),
          volume (translate a t) = volume t := by
        intro a t
        let e : ℝ ≃ᵐ ℝ :=
          { toFun := fun x => -a + x
            invFun := fun x => a + x
            left_inv := by intro x; ring
            right_inv := by intro x; ring
            measurable_toFun := measurable_const.add measurable_id
            measurable_invFun := measurable_const.add measurable_id }
        have h_mp : MeasurePreserving (e : ℝ → ℝ) volume volume :=
          MeasureTheory.measurePreserving_add_left volume (-a)
        have h1 : translate a t = (e : ℝ → ℝ) ⁻¹' t := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, hx, rfl⟩
            simpa [translate, e, Set.mem_preimage] using hx
          · intro hy
            have h2 : -a + y ∈ t := by
              simpa [translate, e, Set.mem_preimage] using hy
            refine ⟨-a + y, h2, by ring⟩
        rw [h1]
        exact h_mp.measure_preimage_equiv t
      have h_badUnion_vol : volume badUnion = 0 := by
        have h1 : volume badUnion ≤
            ∑ g ∈ s, volume (translate (shift' g) (badSet f g I)) :=
          measure_biUnion_finset_le s (fun g => translate (shift' g) (badSet f g I))
        have h2 : ∑ g ∈ s, volume (translate (shift' g) (badSet f g I)) =
            ∑ g ∈ s, volume (badSet f g I) := by
          apply Finset.sum_congr rfl
          intro g _
          exact h_translate_meas (shift' g) (badSet f g I)
        have h3 : ∑ g ∈ s, volume (badSet f g I) = 0 := by
          apply Finset.sum_eq_zero
          intro g _
          exact badSet_measure_zero f g I
        rw [h2, h3] at h1
        exact le_zero_iff.mp h1
      have h_not_sub : ¬ (Set.Icc (-epsilon) epsilon ⊆ badUnion) := by
        intro h_sub
        have h1 : volume (Set.Icc (-epsilon) epsilon) ≤ volume badUnion :=
          measure_mono h_sub
        rw [h_badUnion_vol] at h1
        have h2 : 0 < volume (Set.Icc (-epsilon) epsilon) := by
          simpa [Real.volume_Icc, hepsilon] using by linarith
        have h3 : ¬ (volume (Set.Icc (-epsilon) epsilon) ≤ 0) := not_le.mpr h2
        exact h3 h1
      have h_exists : ∃ (val : ℝ), val ∈ Set.Icc (-epsilon) epsilon ∧ val ∉ badUnion :=
        Set.not_subset.mp h_not_sub
      rcases h_exists with ⟨val, hval_in, hval_notin⟩
      let shift : C2Function → ℝ := fun x => if x = f then val else shift' x
      have h_shift_f : shift f = val := by
        simp [shift]
      have h_shift_other : ∀ (g : C2Function), g ≠ f → shift g = shift' g := by
        intro g hne
        simp [shift, hne]
      refine ⟨shift, ?_, ?_⟩
      · intro g hg
        by_cases h : g = f
        · rw [h, h_shift_f]
          exact abs_le.mpr hval_in
        · rw [h_shift_other g h]
          exact h_bound' g (Finset.mem_insert.mp hg |>.resolve_left h)
      · intro g hg k hk hne
        by_cases hg' : g = f
        · have h_k_ne_f : k ≠ f := by
            intro h
            apply hne
            rw [hg']
            exact Eq.symm h
          have hk' : k ∈ s := Finset.mem_insert.mp hk |>.resolve_left h_k_ne_f
          have h9 : val - shift' k ∉ badSet f k I := by
            have h10 : val ∉ translate (shift' k) (badSet f k I) := by
              have h11 : translate (shift' k) (badSet f k I) ⊆ badUnion := by
                intro y hy
                exact Set.mem_iUnion₂.mpr ⟨k, hk', hy⟩
              intro x
              exact hval_notin (h11 x)
            intro h
            have h11 : val ∈ translate (shift' k) (badSet f k I) := by
              exact ⟨val - shift' k, h, by ring⟩
            exact h10 h11
          have h10 : shift f - shift k ∉ badSet f k I := by
            rw [h_shift_f, h_shift_other k h_k_ne_f]
            exact h9
          have h11 : ∀ x ∈ I.carrier,
              (f.verticalTranslate (shift f)) x ≠ (k.verticalTranslate (shift k)) x ∨
              (f.verticalTranslate (shift f)).firstDeriv x ≠
                (k.verticalTranslate (shift k)).firstDeriv x :=
            (tangency_iff_notin_badSet f k I shift).mpr h10
          simpa [hg'] using h11
        · by_cases hk' : k = f
          · have h_g_ne_f : g ≠ f := by
              intro h
              apply hne
              rw [hk']
              exact h
            have hg'' : g ∈ s := Finset.mem_insert.mp hg |>.resolve_left h_g_ne_f
            have h9 : val ∉ translate (shift' g) (badSet f g I) := by
              have h10 : translate (shift' g) (badSet f g I) ⊆ badUnion := by
                intro y hy
                exact Set.mem_iUnion₂.mpr ⟨g, hg'', hy⟩
              intro x
              exact hval_notin (h10 x)
            have h10 : shift' g - val ∉ badSet g f I := by
              intro h11
              rcases h11 with ⟨x, hx, hderiv, hval⟩
              have h12 : val - shift' g ∈ badSet f g I := by
                refine ⟨x, hx, hderiv.symm, ?_⟩
                linarith
              have h13 : val ∈ translate (shift' g) (badSet f g I) := by
                exact ⟨val - shift' g, h12, by ring⟩
              exact h9 h13
            have h14 : shift g - shift f ∉ badSet g f I := by
              rw [h_shift_other g h_g_ne_f, h_shift_f]
              exact h10
            have h15 : ∀ x ∈ I.carrier,
                (g.verticalTranslate (shift g)) x ≠ (f.verticalTranslate (shift f)) x ∨
                (g.verticalTranslate (shift g)).firstDeriv x ≠
                  (f.verticalTranslate (shift f)).firstDeriv x :=
              (tangency_iff_notin_badSet g f I shift).mpr h14
            simpa [hk'] using h15
          · have hg'' : g ∈ s := Finset.mem_insert.mp hg |>.resolve_left hg'
            have hk'' : k ∈ s := Finset.mem_insert.mp hk |>.resolve_left hk'
            have h12 : shift g = shift' g := h_shift_other g hg'
            have h13 : shift k = shift' k := h_shift_other k hk'
            rw [h12, h13]
            exact h_tang' g hg'' k hk'' hne
  rcases h_main with ⟨shift, h_bound, h_tang⟩
  refine ⟨shift, ?_, ?_⟩
  · intro f hf
    have hf' : f ∈ s := by
      have h : f ∈ (s : Set C2Function) := by
        rw [h_s]
        exact hf
      exact Finset.mem_coe.mp h
    exact h_bound f hf'
  · dsimp only [FiniteFunctionFamily.HasNoExactTangenciesOn]
    intro f hf g hg hne
    have hf' : f ∈ s := by
      have h : f ∈ (s : Set C2Function) := by
        rw [h_s]
        exact hf
      exact Finset.mem_coe.mp h
    have hg' : g ∈ s := by
      have h : g ∈ (s : Set C2Function) := by
        rw [h_s]
        exact hg
      exact Finset.mem_coe.mp h
    exact h_tang f hf' g hg' hne

end Kakeya.Cinematic
