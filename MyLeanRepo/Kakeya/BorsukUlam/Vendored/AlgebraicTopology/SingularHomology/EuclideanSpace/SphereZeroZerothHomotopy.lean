module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.HomologyZeroPathComponents

@[expose] public section

/-!
# Zeroth Homotopy of the Zero-Sphere

This file identifies the zeroth homotopy set of the standard Euclidean
zero-sphere with `Bool`.
-/

noncomputable section

open AlgebraicTopology
open CategoryTheory Limits Metric Preadditive

namespace Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace

/-- The 0-sphere has zeroth homotopy set equivalent to `Bool`. -/
noncomputable def sphereZeroZerothHomotopyEquivBool :
    ZerothHomotopy (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) ≃ Bool := by
  let S0_set : Set (EuclideanSpace ℝ (Fin 1)) := Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
  let S0 := TopCat.of S0_set
  let pt1_val : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 : ℝ)
  let pt2_val : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (-1 : ℝ)
  have h_pt1_val_in : pt1_val ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
    have h : dist pt1_val (0 : EuclideanSpace ℝ (Fin 1)) = 1 := by
      have h1 : dist pt1_val (0 : EuclideanSpace ℝ (Fin 1)) = ‖pt1_val‖ := by
        rw [dist_zero_right]
      rw [h1, PiLp.norm_single]
      norm_num
    simpa [Metric.sphere] using h
  have h_pt2_val_in : pt2_val ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
    have h : dist pt2_val (0 : EuclideanSpace ℝ (Fin 1)) = 1 := by
      have h1 : dist pt2_val (0 : EuclideanSpace ℝ (Fin 1)) = ‖pt2_val‖ := by
        rw [dist_zero_right]
      rw [h1, PiLp.norm_single]
      norm_num
    simpa [Metric.sphere] using h
  let pt1 : S0 := ⟨pt1_val, h_pt1_val_in⟩
  let pt2 : S0 := ⟨pt2_val, h_pt2_val_in⟩
  have h_s0_cases : ∀ (x : S0), x = pt1 ∨ x = pt2 := by
    intro x
    have h_norm : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
      exact norm_eq_of_mem_sphere x
    have h0 : |(x : EuclideanSpace ℝ (Fin 1)) 0| = 1 := by
      have h_norm2 :
          ‖(x : EuclideanSpace ℝ (Fin 1))‖ ^ 2 =
            ∑ i : Fin 1, ((x : EuclideanSpace ℝ (Fin 1)) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ (Fin 1))
      have h_sum :
          (∑ i : Fin 1, ((x : EuclideanSpace ℝ (Fin 1)) i) ^ 2) =
            ((x : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 := by
        rw [Fin.sum_univ_one]
      have h_sq :
          ‖(x : EuclideanSpace ℝ (Fin 1))‖ ^ 2 =
            ((x : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 := by
        rw [h_norm2, h_sum]
      have h_eq1 : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := h_norm
      have h_sq2 : ((x : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
        rw [← h_sq, h_eq1]
        norm_num
      have h_abs : |(x : EuclideanSpace ℝ (Fin 1)) 0| = 1 := by
        have h_pos_or_neg :
            (x : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
              (x : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
          have h :
              ((x : EuclideanSpace ℝ (Fin 1)) 0 - 1) *
                  ((x : EuclideanSpace ℝ (Fin 1)) 0 + 1) =
                0 := by
            linarith
          have h' :
              (x : EuclideanSpace ℝ (Fin 1)) 0 - 1 = 0 ∨
                (x : EuclideanSpace ℝ (Fin 1)) 0 + 1 = 0 :=
            eq_zero_or_eq_zero_of_mul_eq_zero h
          rcases h' with (h' | h')
          · left
            linarith
          · right
            linarith
        rcases h_pos_or_neg with (h_pos | h_neg)
        · rw [h_pos]
          norm_num
        · rw [h_neg]
          norm_num
      exact h_abs
    have h_pos_or_neg :
        (x : EuclideanSpace ℝ (Fin 1)) 0 = 1 ∨
          (x : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
      by_cases h : 0 < (x : EuclideanSpace ℝ (Fin 1)) 0
      · left
        rw [abs_of_pos h] at h0
        linarith
      · right
        have h' : (x : EuclideanSpace ℝ (Fin 1)) 0 ≤ 0 := by
          linarith
        rw [abs_of_nonpos h'] at h0
        linarith
    rcases h_pos_or_neg with (h_eq | h_eq)
    · left
      apply Subtype.ext
      ext i
      fin_cases i
      have h_pt1_eq : (pt1 : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
        dsimp only [pt1, pt1_val]
        simp [EuclideanSpace.single]
      exact Eq.trans h_eq h_pt1_eq.symm
    · right
      apply Subtype.ext
      ext i
      fin_cases i
      have h_pt2_eq : (pt2 : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
        dsimp only [pt2, pt2_val]
        simp [EuclideanSpace.single]
      exact Eq.trans h_eq h_pt2_eq.symm
  have h_pt1_ne_pt2 : pt1 ≠ pt2 := by
    intro h
    have h_val1 : (pt1 : EuclideanSpace ℝ (Fin 1)) = pt1_val := by
      rfl
    have h_val2 : (pt2 : EuclideanSpace ℝ (Fin 1)) = pt2_val := by
      rfl
    have h1 : (pt1 : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
      rw [h_val1]
      have h : pt1_val 0 = (1 : ℝ) := by
        simp [pt1_val, EuclideanSpace.single]
      exact h
    have h2 : (pt2 : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
      rw [h_val2]
      have h : pt2_val 0 = (-1 : ℝ) := by
        simp [pt2_val, EuclideanSpace.single]
      exact h
    have h3 :
        (pt1 : EuclideanSpace ℝ (Fin 1)) 0 = (pt2 : EuclideanSpace ℝ (Fin 1)) 0 :=
      congr_arg (fun (x : S0) => (x : EuclideanSpace ℝ (Fin 1)) 0) h
    rw [h1, h2] at h3
    norm_num at h3
  let g : C(EuclideanSpace ℝ (Fin 1), ℝ) := ⟨fun x => x 0, by fun_prop⟩
  have h_pt1_open : IsOpen ({pt1} : Set S0) := by
    let U : Set (EuclideanSpace ℝ (Fin 1)) := g ⁻¹' (Set.Ioi (0 : ℝ))
    have hU_open : IsOpen U := g.continuous.isOpen_preimage _ isOpen_Ioi
    have h_inter : U ∩ S0_set = {pt1_val} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, U]
      constructor
      · rintro ⟨h_pos, hx⟩
        let y : S0 := ⟨x, hx⟩
        have h_cases : y = pt1 ∨ y = pt2 := h_s0_cases y
        rcases h_cases with (h_eq | h_eq)
        · exact congr_arg (fun (z : S0) => (z : EuclideanSpace ℝ (Fin 1))) h_eq
        · exfalso
          have h_pos' : 0 < g x := by
            simpa [Set.mem_Ioi] using h_pos
          have h_neg' : g x ≤ 0 := by
            have h_eq3 : g x = g pt2_val := by
              congr
              exact congr_arg (fun (z : S0) => (z : EuclideanSpace ℝ (Fin 1))) h_eq
            rw [h_eq3]
            have h41 : g pt2_val = (pt2_val : EuclideanSpace ℝ (Fin 1)) 0 := by
              rfl
            rw [h41]
            simp [pt2_val, EuclideanSpace.single]
          have h_contra : (0 : ℝ) < 0 := lt_of_lt_of_le h_pos' h_neg'
          exact lt_irrefl 0 h_contra
      · rintro rfl
        have h_pos : g pt1_val > 0 := by
          have h1 : g pt1_val = (pt1_val : EuclideanSpace ℝ (Fin 1)) 0 := by
            rfl
          rw [h1]
          simp [pt1_val, EuclideanSpace.single]
        exact ⟨h_pos, pt1.property⟩
    have h : IsOpen (Subtype.val ⁻¹' U : Set S0) := by
      exact hU_open.preimage
        (continuous_subtype_val : Continuous (fun (x : S0) => (x : EuclideanSpace ℝ (Fin 1))))
    have h_eq : (Subtype.val ⁻¹' U : Set S0) = ({pt1} : Set S0) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        have h1 : (x : EuclideanSpace ℝ (Fin 1)) ∈ U ∩ S0_set := ⟨hx, x.property⟩
        rw [h_inter] at h1
        have h2 : (x : EuclideanSpace ℝ (Fin 1)) = pt1_val := by
          simpa using h1
        apply Subtype.ext
        exact h2
      · intro hx
        rw [hx]
        have h1 : pt1_val ∈ U := by
          have h2 : pt1_val ∈ U ∩ S0_set := by
            rw [h_inter]
            simp
          exact h2.1
        exact h1
    rw [← h_eq]
    exact h
  have h_pt2_open : IsOpen ({pt2} : Set S0) := by
    let V : Set (EuclideanSpace ℝ (Fin 1)) := g ⁻¹' (Set.Iio (0 : ℝ))
    have hV_open : IsOpen V := g.continuous.isOpen_preimage _ isOpen_Iio
    have h_inter : V ∩ S0_set = {pt2_val} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, V]
      constructor
      · rintro ⟨h_neg, hx⟩
        let y : S0 := ⟨x, hx⟩
        have h_cases : y = pt1 ∨ y = pt2 := h_s0_cases y
        rcases h_cases with (h_eq | h_eq)
        · exfalso
          have h_eq3 : g x = g pt1_val := by
            congr
            exact congr_arg (fun (z : S0) => (z : EuclideanSpace ℝ (Fin 1))) h_eq
          have h_pos : 0 ≤ g x := by
            rw [h_eq3]
            have h41 : g pt1_val = (pt1_val : EuclideanSpace ℝ (Fin 1)) 0 := by
              rfl
            rw [h41]
            simp [pt1_val, EuclideanSpace.single]
          have h_lt : g x < 0 := by
            simpa [Set.mem_Iio] using h_neg
          have h_contra : g x < g x := by
            calc
              g x < 0 := h_lt
              _ ≤ g x := h_pos
          exact lt_irrefl (g x) h_contra
        · exact congr_arg (fun (z : S0) => (z : EuclideanSpace ℝ (Fin 1))) h_eq
      · rintro rfl
        have h_neg : g pt2_val < 0 := by
          have h1 : g pt2_val = (pt2_val : EuclideanSpace ℝ (Fin 1)) 0 := by
            rfl
          rw [h1]
          simp [pt2_val, EuclideanSpace.single]
        exact ⟨h_neg, pt2.property⟩
    have h : IsOpen (Subtype.val ⁻¹' V : Set S0) := by
      exact hV_open.preimage
        (continuous_subtype_val : Continuous (fun (x : S0) => (x : EuclideanSpace ℝ (Fin 1))))
    have h_eq : (Subtype.val ⁻¹' V : Set S0) = ({pt2} : Set S0) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        have h1 : (x : EuclideanSpace ℝ (Fin 1)) ∈ V ∩ S0_set := ⟨hx, x.property⟩
        rw [h_inter] at h1
        have h2 : (x : EuclideanSpace ℝ (Fin 1)) = pt2_val := by
          simpa using h1
        apply Subtype.ext
        exact h2
      · intro hx
        rw [hx]
        have h1 : pt2_val ∈ V := by
          have h2 : pt2_val ∈ V ∩ S0_set := by
            rw [h_inter]
            simp
          exact h2.1
        exact h1
    rw [← h_eq]
    exact h
  have h_compl : (Set.univ : Set S0) \ {pt1} = {pt2} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_singleton_iff]
    constructor
    · intro hne
      have h : x = pt1 ∨ x = pt2 := h_s0_cases x
      rcases h with (h | h)
      · exfalso
        exact hne h
      · exact h
    · intro h_eq
      rw [h_eq]
      exact h_pt1_ne_pt2.symm
  have h_mk_ne : ZerothHomotopy.mk pt1 ≠ ZerothHomotopy.mk pt2 := by
    intro h
    have h_joined : Joined pt1 pt2 := by
      have h_eq2 : ZerothHomotopy.mk pt1 = ZerothHomotopy.mk pt2 := h
      have h3 :
          (Quotient.mk (pathSetoid S0) pt1 : ZerothHomotopy S0) =
            (Quotient.mk (pathSetoid S0) pt2 : ZerothHomotopy S0) :=
        h_eq2
      have h4 : Joined pt1 pt2 := by
        have h5 :
            (Quotient.mk (pathSetoid S0) pt1 : ZerothHomotopy S0) =
                (Quotient.mk (pathSetoid S0) pt2 : ZerothHomotopy S0) ↔
              Joined pt1 pt2 := by
          exact Quotient.eq'
        exact h5.mp h3
      exact h4
    rcases h_joined with ⟨p⟩
    let U : Set S0 := {pt1}
    have hU_open : IsOpen U := h_pt1_open
    let V : Set S0 := {pt2}
    have hV_open : IsOpen V := h_pt2_open
    let A := p ⁻¹' U
    have hA_open : IsOpen A := p.continuous.isOpen_preimage U hU_open
    let zero : ↥(Set.Icc (0 : ℝ) 1) := ⟨0, by norm_num⟩
    let one : ↥(Set.Icc (0 : ℝ) 1) := ⟨1, by norm_num⟩
    have h0_in : zero ∈ A := by
      have h : p zero = pt1 := p.source
      simpa [A, U] using h
    have h1_notin : one ∉ A := by
      intro h
      have h' : p one = pt1 := h
      have h'' : p one = pt2 := p.target
      rw [h'] at h''
      exact h_pt1_ne_pt2 h''
    have hA_compl : Set.compl A = p ⁻¹' V := by
      ext t
      have h_cases : p t = pt1 ∨ p t = pt2 := h_s0_cases (p t)
      rcases h_cases with (h_eq | h_eq)
      · have h2 : t ∈ A := by
          simp [A, U, h_eq]
        have h4 : t ∉ p ⁻¹' V := by
          intro h5
          have h6 : p t ∈ V := h5
          rw [h_eq] at h6
          have h7 : pt1 ∈ V := h6
          simp [V, h_pt1_ne_pt2] at h7
        constructor
        · intro h_contra
          exfalso
          exact h_contra h2
        · intro h_contra
          exfalso
          exact h4 h_contra
      · have h2 : t ∉ A := by
          intro h_contra
          have h3 : p t ∈ U := h_contra
          rw [h_eq] at h3
          have h7 : pt2 ∈ U := h3
          simp [U] at h7
          exact h_pt1_ne_pt2 h7.symm
        have h4 : t ∈ p ⁻¹' V := by
          simp [V, h_eq]
        constructor
        · intro _
          exact h4
        · intro _
          exact h2
    have h1 : IsOpen (Set.compl A) := by
      have h_eq : Set.compl A = p ⁻¹' V := hA_compl
      rw [h_eq]
      exact p.continuous.isOpen_preimage V hV_open
    have hA_closed : IsClosed A := by
      exact ⟨h1⟩
    have hA_clopen : IsOpen A ∧ IsClosed A := ⟨hA_open, hA_closed⟩
    have h_conn : _root_.IsPreconnected (Set.univ : Set (↥(Set.Icc (0 : ℝ) 1))) := by
      exact isPreconnected_univ
    have h_contra : A = ∅ ∨ A = Set.univ := by
      by_cases h_empty : A = ∅
      · exact Or.inl h_empty
      · by_cases h_full : A = Set.univ
        · exact Or.inr h_full
        · have h1 : (Set.univ ∩ A).Nonempty := by
            rw [Set.univ_inter]
            exact Set.nonempty_iff_ne_empty.mpr h_empty
          let B := Set.compl A
          have hB_open : IsOpen B := hA_closed.isOpen_compl
          have h2 : (Set.univ ∩ B).Nonempty := by
            rw [Set.univ_inter]
            have hB_nonempty : B.Nonempty := by
              by_contra hB_empty
              have hB_empty' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB_empty
              have hA_full : A = Set.univ := by
                have h : Set.compl A = ∅ := hB_empty'
                apply Set.eq_univ_of_univ_subset
                intro x _
                by_contra h_contra
                have h_in_compl : x ∈ Set.compl A := h_contra
                rw [h] at h_in_compl
                simp at h_in_compl
              exact h_full hA_full
            exact hB_nonempty
          have h_subset : (Set.univ : Set (↥(Set.Icc (0 : ℝ) 1))) ⊆ A ∪ B := by
            intro x _
            by_cases h : x ∈ A
            · exact Or.inl h
            · exact Or.inr h
          have h3 : (Set.univ ∩ (A ∩ B)).Nonempty :=
            h_conn A B hA_open hB_open h_subset h1 h2
          exfalso
          have h4 : A ∩ B = (∅ : Set (↥(Set.Icc (0 : ℝ) 1))) := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
            intro h
            exact h.2 h.1
          rw [h4] at h3
          simp at h3
    rcases h_contra with (h_empty | h_full)
    · rw [h_empty] at h0_in
      simp at h0_in
    · rw [h_full] at h1_notin
      exact h1_notin (Set.mem_univ one)
  classical
  refine
    { toFun := fun z => if z = ZerothHomotopy.mk pt1 then true else false
      invFun := fun b => if b then ZerothHomotopy.mk pt1 else ZerothHomotopy.mk pt2
      left_inv := by
        intro z
        obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
        rcases h_s0_cases x with (rfl | rfl)
        · simp
        · simp [h_mk_ne.symm]
      right_inv := by
        intro b
        fin_cases b
        · simp
        · simp [h_mk_ne.symm] }

end Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace
