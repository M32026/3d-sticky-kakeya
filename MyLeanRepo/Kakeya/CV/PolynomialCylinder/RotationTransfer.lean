import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationReduction
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import Mathlib.Algebra.MvPolynomial.PDeriv

noncomputable section

open MeasureTheory Metric Set MvPolynomial
open scoped ENNReal NNReal Real

namespace Kakeya.CV

variable (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)

/-- Standard basis vector e_i. -/
def eBasis (i : Fin 3) : Point 3 := EuclideanSpace.single i 1

/-- The substitution polynomial for variable `i`. -/
def rotSubst (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ j : Fin 3, (R.symm (eBasis j)) i • MvPolynomial.X j

/-- The rotated polynomial. -/
def rotatedPoly (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C (rotSubst R) p

/-- The inverse substitution. -/
def invRotSubst (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, (R (eBasis i)) j • MvPolynomial.X i

/-- inner product with basis vector extracts component. -/
lemma inner_eBasis_right (v : Point 3) (i : Fin 3) : inner ℝ v (eBasis i) = v i := by
  have h1 : inner ℝ v (eBasis i) = ∑ j : Fin 3, inner ℝ (v j) ((eBasis i) j) := by
    rw [PiLp.inner_apply]
  rw [h1]
  have h2 : ∑ j : Fin 3, inner ℝ (v j) ((eBasis i) j) = ∑ j : Fin 3, v j * (eBasis i) j := by
    apply Finset.sum_congr rfl
    intro j _
    exact Real.inner_apply _ _
  rw [h2]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp [eBasis]
  · intro j _ hne
    simp [eBasis, hne]

/-- Euclidean basis decomposition. -/
lemma euclidean_basis_decomp (v : Point 3) : v = ∑ k : Fin 3, v k • eBasis k := by
  ext i
  have h_sum : (∑ k : Fin 3, v k • eBasis k) i = ∑ k : Fin 3, (v k • eBasis k) i := by
    exact Real.ext_cauchy rfl
  rw [h_sum]
  have h2 : ∑ k : Fin 3, (v k • eBasis k) i = v i := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [eBasis, smul_eq_mul, EuclideanSpace.single_apply]
    · intro k _ hne
      simp [eBasis, hne, smul_eq_mul, EuclideanSpace.single_apply]
  exact h2.symm

/-- Adjoint identity: (R.symm(e_j))_i = (R(e_i))_j. -/
lemma adjoint_identity (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (i j : Fin 3) :
    (R.symm (eBasis j)) i = (R (eBasis i)) j := by
  have h1 : (R.symm (eBasis j)) i = inner ℝ (R.symm (eBasis j)) (eBasis i) :=
    (inner_eBasis_right (R.symm (eBasis j)) i).symm
  rw [h1]
  have h2 : inner ℝ (R.symm (eBasis j)) (eBasis i) = inner ℝ (eBasis j) (R (eBasis i)) := by
    calc inner ℝ (R.symm (eBasis j)) (eBasis i)
      = inner ℝ (R (R.symm (eBasis j))) (R (eBasis i)) := by rw [R.inner_map_map]
    _ = inner ℝ (eBasis j) (R (eBasis i)) := by rw [R.apply_symm_apply]
  rw [h2]
  have h3 : inner ℝ (eBasis j) (R (eBasis i)) = inner ℝ (R (eBasis i)) (eBasis j) := by
    exact real_inner_comm _ _
  rw [h3]
  exact inner_eBasis_right (R (eBasis i)) j

/-- Matrix identity: ∑ j, (R.symm e_j)_i * (R x)_j = x_i. -/
lemma matrix_identity (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (x : Point 3) (i : Fin 3) :
    ∑ j : Fin 3, (R.symm (eBasis j)) i * (R x) j = x i := by
  have h_adj : ∀ j : Fin 3, (R.symm (eBasis j)) i = (R (eBasis i)) j :=
    fun j => adjoint_identity R i j
  have h_sum : ∑ j : Fin 3, (R.symm (eBasis j)) i * (R x) j =
      ∑ j : Fin 3, (R x) j * (R (eBasis i)) j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [h_adj j] <;> ring
  rw [h_sum]
  have h_inner1 : inner ℝ (R x) (R (eBasis i)) = ∑ j : Fin 3, (R x) j * (R (eBasis i)) j := by
    have h : inner ℝ (R x) (R (eBasis i)) = ∑ j : Fin 3, inner ℝ ((R x) j) ((R (eBasis i)) j) := by
      rw [PiLp.inner_apply]
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    exact Real.inner_apply _ _
  have h_inner2 : ∑ j : Fin 3, (R x) j * (R (eBasis i)) j = inner ℝ (R x) (R (eBasis i)) :=
    h_inner1.symm
  rw [h_inner2]
  have h_isom : inner ℝ (R x) (R (eBasis i)) = inner ℝ x (eBasis i) := by
    rw [R.inner_map_map]
  rw [h_isom]
  exact inner_eBasis_right x i

/-- Key identity: polynomialValue (rotatedPoly p R) (R x) = polynomialValue p x. -/
lemma rotatedPoly_eval (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (x : Point 3) :
    polynomialValue (rotatedPoly p R) (R x) = polynomialValue p x := by
  let g := rotSubst R
  let y : Fin 3 → ℝ := fun i => (R x) i
  have h_comp : MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C g p) =
      MvPolynomial.eval (fun i => x i) p := by
    rw [MvPolynomial.eval_eval₂ (f := MvPolynomial.C) (g := g) (p := p)]
    have h_id : (MvPolynomial.eval y).comp MvPolynomial.C = RingHom.id ℝ := by
      ext r
      simp
    rw [h_id]
    congr with i
    simpa [g, rotSubst, MvPolynomial.eval_sum, MvPolynomial.eval_X, MvPolynomial.eval_C]
      using matrix_identity R x i
  simpa [polynomialValue, rotatedPoly] using h_comp

/-- Composing inverse substitution with substitution gives identity. -/
lemma subst_compose_identity (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (i : Fin 3) :
    MvPolynomial.eval₂ MvPolynomial.C (invRotSubst R) (rotSubst R i) = MvPolynomial.X i := by
  let e : Fin 3 → Point 3 := eBasis
  let khom : MvPolynomial (Fin 3) ℝ →+* MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (invRotSubst R)
  have h_def : rotSubst R i = ∑ j : Fin 3, (R.symm (e j)) i • MvPolynomial.X j := by rfl
  have h1 : khom (rotSubst R i) = ∑ j : Fin 3, (R.symm (e j)) i • khom (MvPolynomial.X j) := by
    rw [h_def]
    have h_sum : khom (∑ j : Fin 3, (R.symm (e j)) i • MvPolynomial.X j) =
        ∑ j : Fin 3, khom ((R.symm (e j)) i • MvPolynomial.X j) := by
      exact map_sum khom _ _
    rw [h_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h2 : khom ((R.symm (e j)) i • MvPolynomial.X j) =
        (R.symm (e j)) i • khom (MvPolynomial.X j) := by
      let c : ℝ := (R.symm (e j)) i
      have h_smul1 : c • MvPolynomial.X j = MvPolynomial.C c * MvPolynomial.X j := by
        exact smul_eq_C_mul (MvPolynomial.X j) c
      rw [h_smul1]
      have h_mul : khom (MvPolynomial.C c * MvPolynomial.X j) =
          khom (MvPolynomial.C c) * khom (MvPolynomial.X j) := khom.map_mul _ _
      rw [h_mul]
      have h_C : khom (MvPolynomial.C c) = MvPolynomial.C c := by
        simp [khom, MvPolynomial.eval₂Hom]
      rw [h_C]
      have h_final : MvPolynomial.C c * khom (MvPolynomial.X j) =
          c • khom (MvPolynomial.X j) := by
        exact MvPolynomial.C_mul'
      exact h_final
    exact h2
  have h_X : ∀ j : Fin 3, khom (MvPolynomial.X j) = invRotSubst R j := by
    intro j
    simp [khom]
  have h2 : khom (rotSubst R i) = ∑ j : Fin 3, (R.symm (e j)) i • invRotSubst R j := by
    calc khom (rotSubst R i)
      = ∑ j : Fin 3, (R.symm (e j)) i • khom (MvPolynomial.X j) := h1
    _ = ∑ j : Fin 3, (R.symm (e j)) i • invRotSubst R j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h_X j]
  have h_main : ∑ j : Fin 3, (R.symm (e j)) i • invRotSubst R j = MvPolynomial.X i := by
    have h1 : ∑ j : Fin 3, (R.symm (e j)) i • invRotSubst R j =
        ∑ j : Fin 3, (R.symm (e j)) i • (∑ k : Fin 3, (R (e k)) j • MvPolynomial.X k) := by
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [h1]
    let c : Fin 3 → ℝ := fun j => (R.symm (e j)) i
    let d : Fin 3 → Fin 3 → ℝ := fun j k => (R (e k)) j
    have h2 : ∑ j : Fin 3, MvPolynomial.C (c j) * (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) =
        ∑ j : Fin 3, ∑ k : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k := by
      apply Finset.sum_congr rfl
      intro j _
      have h_goal : MvPolynomial.C (c j) * (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) =
          ∑ k : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k := by
        let mul_Cj : MvPolynomial (Fin 3) ℝ →+ MvPolynomial (Fin 3) ℝ :=
          { toFun := fun p => MvPolynomial.C (c j) * p
            map_zero' := by simp
            map_add' := by intro p q; ring }
        have h_eq1 : MvPolynomial.C (c j) * (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) =
            mul_Cj (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) := by rfl
        rw [h_eq1]
        have h_mul_sum : mul_Cj (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) =
            ∑ k : Fin 3, mul_Cj (MvPolynomial.C (d j k) * MvPolynomial.X k) := by
          exact map_sum mul_Cj (fun k => MvPolynomial.C (d j k) * MvPolynomial.X k) (Finset.univ)
        rw [h_mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have h_C_mul : MvPolynomial.C (c j) * (MvPolynomial.C (d j k) * MvPolynomial.X k) =
            MvPolynomial.C (c j * d j k) * MvPolynomial.X k := by
          have h1 : (MvPolynomial.C (c j) : MvPolynomial (Fin 3) ℝ) * MvPolynomial.C (d j k) = MvPolynomial.C (c j * d j k) := by
            simpa [MvPolynomial.C_mul'] using rfl
          rw [← mul_assoc, h1]
        exact h_C_mul
      exact h_goal
    have h_smul_eq : ∀ (x : ℝ) (p : MvPolynomial (Fin 3) ℝ), x • p = MvPolynomial.C x * p := by
      intro x p
      exact smul_eq_C_mul p x
    have h_goal1 : ∑ j : Fin 3, c j • (∑ k : Fin 3, d j k • MvPolynomial.X k) =
        ∑ j : Fin 3, MvPolynomial.C (c j) * (∑ k : Fin 3, MvPolynomial.C (d j k) * MvPolynomial.X k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h_smul_eq (c j)]
      apply congr_arg (fun p => MvPolynomial.C (c j) * p)
      apply Finset.sum_congr rfl
      intro k _
      exact h_smul_eq (d j k) (MvPolynomial.X k)
    rw [h_goal1]
    rw [h2]
    -- Goal: ∑ j, ∑ k, C(c j * d j k) * X k = X i
    have h3 : ∑ j : Fin 3, ∑ k : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k =
        ∑ k : Fin 3, ∑ j : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k := by
      rw [Finset.sum_comm]
    rw [h3]
    have h4 : ∑ k : Fin 3, ∑ j : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k =
        ∑ k : Fin 3, MvPolynomial.C (∑ j : Fin 3, c j * d j k) * MvPolynomial.X k := by
      apply Finset.sum_congr rfl
      intro k _
      have h_sum_mul : ∑ j : Fin 3, MvPolynomial.C (c j * d j k) * MvPolynomial.X k =
          (∑ j : Fin 3, MvPolynomial.C (c j * d j k)) * MvPolynomial.X k := by
        rw [Finset.sum_mul]
      rw [h_sum_mul]
      have h_C_sum : (∑ j : Fin 3, (MvPolynomial.C (c j * d j k) : MvPolynomial (Fin 3) ℝ)) =
          (MvPolynomial.C (∑ j : Fin 3, c j * d j k) : MvPolynomial (Fin 3) ℝ) := by
        rw [map_sum (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 3) ℝ)]
      rw [h_C_sum]
    rw [h4]
    have h_coeff : ∀ k : Fin 3, (∑ j : Fin 3, c j * d j k) = (e k) i := by
      intro k
      simpa [c, d, e] using matrix_identity R (e k) i
    rw [Finset.sum_congr rfl (fun k _ => by rw [h_coeff k])]
    have h_final : ∑ k : Fin 3, MvPolynomial.C ((e k) i) * MvPolynomial.X k = MvPolynomial.X i := by
      have h_eii : (e i) i = 1 := by
        simp [e, eBasis]
        <;> decide
      have h_eki : ∀ (k : Fin 3), k ≠ i → (e k) i = 0 := by
        intro k hne
        simp [e, eBasis, hne]
        <;> decide
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [h_eii]
        <;> simp
      · intro k _ hne
        rw [h_eki k hne]
        <;> simp
    exact h_final
  have h_goal : MvPolynomial.eval₂ MvPolynomial.C (invRotSubst R) (rotSubst R i) = MvPolynomial.X i := by
    have h_eq : MvPolynomial.eval₂ MvPolynomial.C (invRotSubst R) (rotSubst R i) = khom (rotSubst R i) := by rfl
    rw [h_eq, h2, h_main]
  exact h_goal

/-- rotatedPoly p R ≠ 0 when p ≠ 0. -/
lemma rotatedPoly_ne_zero (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (hp : p ≠ 0) : rotatedPoly p R ≠ 0 := by
  let p' := rotatedPoly p R
  let h := invRotSubst R
  let khom : MvPolynomial (Fin 3) ℝ →+* MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.eval₂Hom MvPolynomial.C h
  have h_p'_def : p' = MvPolynomial.eval₂ MvPolynomial.C (rotSubst R) p := by rfl
  have h_comp : khom p' = p := by
    have h_eval₂ : khom (MvPolynomial.eval₂ MvPolynomial.C (rotSubst R) p) =
        MvPolynomial.eval₂ (khom.comp MvPolynomial.C) (fun i => khom (rotSubst R i)) p :=
      MvPolynomial.eval₂_comp_left khom MvPolynomial.C (rotSubst R) p
    have h_kC : khom.comp MvPolynomial.C = MvPolynomial.C := by
      ext r
      simp [khom]
    have h1 : khom p' = MvPolynomial.eval₂ MvPolynomial.C (fun i => khom (rotSubst R i)) p := by
      rw [h_p'_def]
      rw [h_eval₂, h_kC]
    rw [h1]
    have h2 : (fun i : Fin 3 => khom (rotSubst R i)) = MvPolynomial.X := by
      funext i
      have h3 : khom (rotSubst R i) = MvPolynomial.eval₂ MvPolynomial.C h (rotSubst R i) := by rfl
      rw [h3]
      exact subst_compose_identity R i
    rw [h2]
    exact MvPolynomial.eval₂_eta p
  intro h_contra
  have h_contra' : p' = 0 := by exact h_contra
  have h' : khom p' = 0 := by
    rw [h_contra'] <;> simp
  have h'' : p = 0 := by
    calc p = khom p' := h_comp.symm
         _ = 0 := h'
  exact hp h''

/-- Total degree is non-increasing under linear substitution. -/
lemma rotatedPoly_totalDegree_le (p : MvPolynomial (Fin 3) ℝ)
    (R : Point 3 ≃ₗᵢ[ℝ] Point 3) :
    (rotatedPoly p R).totalDegree ≤ p.totalDegree := by
  let g := rotSubst R
  have h1 : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    have h_g : g i = ∑ j : Fin 3, (R.symm (eBasis j)) i • MvPolynomial.X j := by rfl
    rw [h_g]
    let Xj : Fin 3 → MvPolynomial (Fin 3) ℝ := fun j => MvPolynomial.X j
    let c : Fin 3 → ℝ := fun j => (R.symm (eBasis j)) i
    have h_each : ∀ j ∈ (Finset.univ : Finset (Fin 3)), (c j • Xj j).totalDegree ≤ 1 := by
      intro j _
      have h4 : (c j • Xj j).totalDegree ≤ (Xj j).totalDegree :=
        MvPolynomial.totalDegree_smul_le (c j) (Xj j)
      have h5 : (Xj j).totalDegree = 1 := MvPolynomial.totalDegree_X j
      rw [h5] at h4
      exact h4
    exact MvPolynomial.totalDegree_finsetSum_le (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j : Fin 3 => c j • Xj j) (d := 1) h_each
  have h_rot : rotatedPoly p R = MvPolynomial.eval₂ MvPolynomial.C g p := by rfl
  rw [h_rot]
  rw [MvPolynomial.eval₂_eq MvPolynomial.C g p]
  let F : (Fin 3 →₀ ℕ) → MvPolynomial (Fin 3) ℝ := fun d =>
    MvPolynomial.C (MvPolynomial.coeff d p) * ∏ i ∈ d.support, g i ^ d i
  have h_main : ∀ d ∈ p.support, (F d).totalDegree ≤ p.totalDegree := by
    intro d hd
    have h5 : (F d).totalDegree ≤ (∏ i ∈ d.support, g i ^ d i).totalDegree := by
      dsimp only [F]
      calc
        (MvPolynomial.C (MvPolynomial.coeff d p) * ∏ i ∈ d.support, g i ^ d i).totalDegree
          ≤ (MvPolynomial.C (MvPolynomial.coeff d p)).totalDegree + (∏ i ∈ d.support, g i ^ d i).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ = (∏ i ∈ d.support, g i ^ d i).totalDegree := by
          rw [MvPolynomial.totalDegree_C, zero_add]
    apply h5.trans
    have h6 : (∏ i ∈ d.support, g i ^ d i).totalDegree ≤ ∑ i ∈ d.support, (g i ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    apply h6.trans
    have h7 : ∑ i ∈ d.support, (g i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i * (g i).totalDegree := by
      apply Finset.sum_le_sum
      intro i _
      exact MvPolynomial.totalDegree_pow (g i) (d i)
    apply h7.trans
    have h8 : ∑ i ∈ d.support, d i * (g i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      have h9 : d i * (g i).totalDegree ≤ d i := by
        calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left (d i) (h1 i)
             _ = d i := by ring
      exact h9
    apply h8.trans
    have h10 : (Finsupp.toMultiset d).card = ∑ i ∈ d.support, d i := by
      have h_card : (Finsupp.toMultiset d).card = Finsupp.sum d (fun _ n => n) := by
        exact Finsupp.card_toMultiset d
      have h_sum : Finsupp.sum d (fun _ : Fin 3 => fun n : ℕ => n) = ∑ i ∈ d.support, d i := by
        simp [Finsupp.sum]
      rw [h_card, h_sum]
    have h11 : (Finsupp.toMultiset d).card ≤ p.totalDegree := by
      rw [MvPolynomial.totalDegree_eq]
      have h_sup : (Finsupp.toMultiset d).card ≤ p.support.sup (fun m : Fin 3 →₀ ℕ => (Finsupp.toMultiset m).card) :=
        Finset.le_sup (f := (fun m : Fin 3 →₀ ℕ => (Finsupp.toMultiset m).card)) hd
      exact h_sup
    rw [h10] at h11
    exact h11
  exact MvPolynomial.totalDegree_finsetSum_le (s := p.support) (f := F) (d := p.totalDegree) h_main

/-- Chain rule for pderiv under polynomial substitution. -/
lemma pderiv_eval₂_chain {n : ℕ} {R : Type*} [CommSemiring R]
    (g : Fin n → MvPolynomial (Fin n) R) (p : MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g p) =
    ∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) *
      MvPolynomial.pderiv i (g k) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.eval₂_C]
  | add p q hp hq =>
    have h_pderiv_add : ∀ k : Fin n, MvPolynomial.pderiv k (p + q) =
        MvPolynomial.pderiv k p + MvPolynomial.pderiv k q := by
      intro k
      exact (MvPolynomial.pderiv k).map_add p q
    calc
      MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g (p + q))
        = MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g p + MvPolynomial.eval₂ MvPolynomial.C g q) := by
          rw [MvPolynomial.eval₂_add]
      _ = MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g p) +
            MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g q) := by
          exact (MvPolynomial.pderiv i).map_add _ _
      _ = (∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) *
              MvPolynomial.pderiv i (g k)) +
            (∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k q)) *
              MvPolynomial.pderiv i (g k)) := by
          rw [hp, hq]
      _ = ∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k (p + q))) *
              MvPolynomial.pderiv i (g k) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [h_pderiv_add k, MvPolynomial.eval₂_add] <;> ring
  | mul_X p j hp =>
    have h_eval : MvPolynomial.eval₂ MvPolynomial.C g (p * MvPolynomial.X j) =
        (MvPolynomial.eval₂ MvPolynomial.C g p) * g j := by
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] <;> ring
    have h_pderiv_k : ∀ k : Fin n, MvPolynomial.pderiv k (p * MvPolynomial.X j) =
        (MvPolynomial.pderiv k p) * MvPolynomial.X j + if k = j then p else 0 := by
      intro k
      have h_main : MvPolynomial.pderiv k (p * MvPolynomial.X j) =
          MvPolynomial.pderiv k p * MvPolynomial.X j + p * MvPolynomial.pderiv k (MvPolynomial.X j) :=
        MvPolynomial.pderiv_mul
      rw [h_main]
      by_cases h : k = j
      · subst h
        rw [MvPolynomial.pderiv_X_self]
        <;> simp
      · have h' : j ≠ k := by tauto
        rw [MvPolynomial.pderiv_X_of_ne h']
        <;> simp [h]
    have h_eval₂_k : ∀ k : Fin n, MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k (p * MvPolynomial.X j)) =
        (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * g j +
          if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0 := by
      intro k
      rw [h_pderiv_k k]
      rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      split_ifs <;> simp [MvPolynomial.eval₂_C] <;> ring
    have h_rhs : ∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k (p * MvPolynomial.X j))) *
            MvPolynomial.pderiv i (g k) =
        (∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) *
          MvPolynomial.pderiv i (g k)) * g j +
        (MvPolynomial.eval₂ MvPolynomial.C g p) * MvPolynomial.pderiv i (g j) := by
      have h3 : ∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k (p * MvPolynomial.X j))) *
              MvPolynomial.pderiv i (g k) =
          ∑ k : Fin n, ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * g j +
              if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) *
            MvPolynomial.pderiv i (g k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_eval₂_k k]
      rw [h3]
      have h4 : ∑ k : Fin n, ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * g j +
              if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) *
            MvPolynomial.pderiv i (g k) =
          ∑ k : Fin n, ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * MvPolynomial.pderiv i (g k)) * g j +
          ∑ k : Fin n, (if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) * MvPolynomial.pderiv i (g k) := by
        have h_distrib : ∀ k : Fin n,
            ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * g j +
              if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) *
            MvPolynomial.pderiv i (g k) =
            ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * MvPolynomial.pderiv i (g k)) * g j +
            (if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) * MvPolynomial.pderiv i (g k) := by
          intro k; ring
        rw [Finset.sum_congr rfl (fun x _ => h_distrib x)]
        rw [Finset.sum_add_distrib]
      rw [h4]
      have h5 : ∑ k : Fin n, ((MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * MvPolynomial.pderiv i (g k)) * g j =
          (∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) * MvPolynomial.pderiv i (g k)) * g j := by
        rw [Finset.sum_mul]
      have h6 : ∑ k : Fin n, (if k = j then MvPolynomial.eval₂ MvPolynomial.C g p else 0) * MvPolynomial.pderiv i (g k) =
          (MvPolynomial.eval₂ MvPolynomial.C g p) * MvPolynomial.pderiv i (g j) := by
        rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
        · simp
        · intro k _ hne
          rw [if_neg hne] <;> simp
      rw [h5, h6] <;> ring
    calc
      MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g (p * MvPolynomial.X j))
        = MvPolynomial.pderiv i ((MvPolynomial.eval₂ MvPolynomial.C g p) * g j) := by rw [h_eval]
      _ = (MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C g p)) * g j +
            (MvPolynomial.eval₂ MvPolynomial.C g p) * MvPolynomial.pderiv i (g j) := by
          rw [MvPolynomial.pderiv_mul]
      _ = (∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) *
              MvPolynomial.pderiv i (g k)) * g j +
            (MvPolynomial.eval₂ MvPolynomial.C g p) * MvPolynomial.pderiv i (g j) := by
          rw [hp] <;> ring
      _ = ∑ k : Fin n, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k (p * MvPolynomial.X j))) *
              MvPolynomial.pderiv i (g k) := by
          exact h_rhs.symm

/-- Gradient transforms linearly under rotation. -/
lemma rotatedPoly_gradient (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (x : Point 3) :
    polynomialGradient (rotatedPoly p R) (R x) = R (polynomialGradient p x) := by
  let g := rotSubst R
  let p' := rotatedPoly p R
  have h_chain : ∀ i : Fin 3,
      MvPolynomial.pderiv i p' =
      ∑ k : Fin 3, (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) *
        MvPolynomial.pderiv i (g k) := by
    intro i
    exact pderiv_eval₂_chain g p i
  have h_pderiv_g : ∀ i k : Fin 3,
      MvPolynomial.pderiv i (g k) = MvPolynomial.C ((R.symm (eBasis i)) k) := by
    intro i k
    have h_def : g k = ∑ j : Fin 3, (R.symm (eBasis j)) k • MvPolynomial.X j := by rfl
    rw [h_def]
    let D : MvPolynomial (Fin 3) ℝ →+ MvPolynomial (Fin 3) ℝ :=
      (MvPolynomial.pderiv i).toAddMonoidHom
    have h_sum : D (∑ j : Fin 3, (R.symm (eBasis j)) k • MvPolynomial.X j) =
        ∑ j : Fin 3, D ((R.symm (eBasis j)) k • MvPolynomial.X j) := by
      exact map_sum D _ _
    have h_deriveq : (MvPolynomial.pderiv i) (∑ j : Fin 3, (R.symm (eBasis j)) k • MvPolynomial.X j) =
        D (∑ j : Fin 3, (R.symm (eBasis j)) k • MvPolynomial.X j) := by rfl
    rw [h_deriveq, h_sum]
    have h_each : ∑ j : Fin 3, D ((R.symm (eBasis j)) k • MvPolynomial.X j) =
        ∑ j : Fin 3, (R.symm (eBasis j)) k • (MvPolynomial.pderiv i) (MvPolynomial.X j) := by
      apply Finset.sum_congr rfl
      intro j _
      let c : ℝ := (R.symm (eBasis j)) k
      have h_D_eq : ∀ q, D q = (MvPolynomial.pderiv i) q := by intro q; rfl
      have h_goal : D (c • MvPolynomial.X j) = c • (MvPolynomial.pderiv i) (MvPolynomial.X j) := by
        rw [h_D_eq]
        have h1 : c • MvPolynomial.X j = MvPolynomial.C c * MvPolynomial.X j := by
          exact smul_eq_C_mul (MvPolynomial.X j) c
        rw [h1, MvPolynomial.pderiv_C_mul]
        have h2 : MvPolynomial.C c * (MvPolynomial.pderiv i) (MvPolynomial.X j) =
            c • (MvPolynomial.pderiv i) (MvPolynomial.X j) := by
          exact MvPolynomial.C_mul'
        exact h2
      exact h_goal
    rw [h_each]
    have h3 : ∑ j : Fin 3, (R.symm (eBasis j)) k • (MvPolynomial.pderiv i) (MvPolynomial.X j) =
        (R.symm (eBasis i)) k • (1 : MvPolynomial (Fin 3) ℝ) := by
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · simp [MvPolynomial.pderiv_X_self]
      · intro j _ hne
        rw [MvPolynomial.pderiv_X_of_ne hne]
        <;> simp
    rw [h3]
    have h4 : (R.symm (eBasis i)) k • (1 : MvPolynomial (Fin 3) ℝ) =
        MvPolynomial.C ((R.symm (eBasis i)) k) := by
      exact Eq.symm MvPolynomial.C_eq_smul_one
    exact h4
  have h_adjoint : ∀ (i k : Fin 3), (R.symm (eBasis i)) k = (R (eBasis k)) i :=
    fun i k => adjoint_identity R k i
  ext i
  have h_step1 : polynomialValue (MvPolynomial.pderiv i p') (R x) =
      ∑ k : Fin 3, polynomialValue (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) (R x) *
        polynomialValue (MvPolynomial.pderiv i (g k)) (R x) := by
    rw [h_chain i]
    simp [polynomialValue, MvPolynomial.eval_mul]
    <;> rfl
  have h_step2 : ∀ k, polynomialValue (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.pderiv k p)) (R x) =
      polynomialValue (MvPolynomial.pderiv k p) x := by
    intro k
    exact rotatedPoly_eval (MvPolynomial.pderiv k p) R x
  have h_step3 : ∀ k, polynomialValue (MvPolynomial.pderiv i (g k)) (R x) = (R.symm (eBasis i)) k := by
    intro k
    rw [h_pderiv_g i k]
    <;> simp [polynomialValue, MvPolynomial.eval_C]
  have h_eval : polynomialValue (MvPolynomial.pderiv i p') (R x) =
      ∑ k : Fin 3, polynomialValue (MvPolynomial.pderiv k p) x * (R (eBasis k)) i := by
    rw [h_step1]
    rw [Finset.sum_congr rfl (fun k _ => by
      rw [h_step2 k, h_step3 k, h_adjoint i k] <;> ring)]
  have h_main : (polynomialGradient p' (R x)) i =
      ∑ k : Fin 3, (polynomialGradient p x) k * (R (eBasis k)) i := by
    simpa [polynomialGradient] using h_eval
  have h_decomp : polynomialGradient p x = ∑ j : Fin 3, (polynomialGradient p x) j • eBasis j :=
    euclidean_basis_decomp (polynomialGradient p x)
  have h2 : R (polynomialGradient p x) = ∑ j : Fin 3, (polynomialGradient p x) j • R (eBasis j) := by
    calc
      R (polynomialGradient p x)
        = R (∑ j : Fin 3, (polynomialGradient p x) j • eBasis j) := by exact congr_arg R h_decomp
      _ = ∑ j : Fin 3, R ((polynomialGradient p x) j • eBasis j) := by exact map_sum R _ _
      _ = ∑ j : Fin 3, (polynomialGradient p x) j • R (eBasis j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact R.map_smul ((polynomialGradient p x) j) (eBasis j)
  have h3 : (R (polynomialGradient p x)) i =
      ∑ k : Fin 3, (polynomialGradient p x) k * (R (eBasis k)) i := by
    rw [h2]
    have h4 : (∑ j : Fin 3, (polynomialGradient p x) j • R (eBasis j)) i =
        ∑ j : Fin 3, ((polynomialGradient p x) j • R (eBasis j)) i := by
      exact Real.ext_cauchy rfl
    rw [h4]
    apply Finset.sum_congr rfl
    intro j _
    simp [smul_eq_mul]
    <;> ring
  rw [h_main, h3]

/-- Unit normal transforms linearly under rotation. -/
lemma rotatedPoly_unitNormal (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (x : Point 3) :
    polynomialUnitNormal (rotatedPoly p R) (R x) = R (polynomialUnitNormal p x) := by
  let p' := rotatedPoly p R
  have h_grad : polynomialGradient p' (R x) = R (polynomialGradient p x) :=
    rotatedPoly_gradient p R x
  have h_norm : ‖polynomialGradient p' (R x)‖ = ‖polynomialGradient p x‖ := by
    rw [h_grad]
    exact R.norm_map (polynomialGradient p x)
  by_cases h : ‖polynomialGradient p x‖ = 0
  · have hgz : polynomialGradient p x = 0 := by
      simpa [norm_eq_zero] using h
    have hgz' : polynomialGradient p' (R x) = 0 := by
      rw [h_grad, hgz] <;> simp
    have h' : ‖polynomialGradient p' (R x)‖ = 0 := by
      rw [h_norm] <;> exact h
    rw [polynomialUnitNormal, polynomialUnitNormal]
    rw [dif_pos h, dif_pos h']
    <;> simp
  · have h' : ‖polynomialGradient p' (R x)‖ ≠ 0 := by
      rw [h_norm] <;> exact h
    rw [polynomialUnitNormal, polynomialUnitNormal]
    rw [dif_neg h, dif_neg h']
    rw [h_grad]
    have h_norm2 : ‖R (polynomialGradient p x)‖ = ‖polynomialGradient p x‖ :=
      R.norm_map (polynomialGradient p x)
    rw [h_norm2]
    rw [← R.map_smul]
    <;> rfl

/-- R maps polynomial zero set to zero set of rotated polynomial. -/
lemma rotated_zeroSet (p : MvPolynomial (Fin 3) ℝ) (R : Point 3 ≃ₗᵢ[ℝ] Point 3) :
    R '' polynomialZeroSet p = polynomialZeroSet (rotatedPoly p R) := by
  let p' := rotatedPoly p R
  ext y
  simp only [Set.mem_image, polynomialZeroSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h := rotatedPoly_eval p R x
    rw [hx] at h
    exact h
  · intro hy
    let x := R.symm y
    have hRx : R x = y := R.right_inv y
    have hxp : polynomialValue p x = 0 := by
      have h := rotatedPoly_eval p R x
      rw [hRx] at h
      exact h.symm.trans hy
    exact ⟨x, hxp, hRx⟩

/-- R maps unit tube to unit tube about rotated line. -/
lemma rotated_unitTube (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (a : Point 3) (e : Point 3)
    (hRe : R e = e3) :
    R '' unitTube a e = unitTube (R a) e3 := by
  have h_line : R '' affineLine a e = affineLine (R a) e3 := by
    ext y
    simp only [Set.mem_image, affineLine, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      refine' ⟨t, _⟩
      have h : R (a + t • e) = R a + t • e3 := by
        rw [R.map_add, R.map_smul, hRe] <;> abel
      exact h
    · rintro ⟨t, ht⟩
      refine' ⟨a + t • e, ⟨t, rfl⟩, _⟩
      have h : R (a + t • e) = R a + t • e3 := by
        rw [R.map_add, R.map_smul, hRe] <;> abel
      rw [h, ht]
  have h_isom : Isometry (R : Point 3 → Point 3) :=
    LinearIsometryEquiv.isometry R
  have h_inf : ∀ (z : Point 3), Metric.infDist (R z) (R '' affineLine a e) =
      Metric.infDist z (affineLine a e) := by
    intro z
    exact Metric.infDist_image h_isom
  ext y
  simp only [Set.mem_image, unitTube, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h_line] at *
    <;> exact (h_inf x).symm ▸ hx
  · intro hy
    let x := R.symm y
    have hRx : R x = y := R.right_inv y
    have h_y : y = R x := hRx.symm
    have h_isom2 : Metric.infDist y (affineLine (R a) e3) = Metric.infDist x (affineLine a e) := by
      rw [h_y, ← h_line]
      exact h_inf x
    rw [h_isom2] at hy
    exact ⟨x, hy, hRx⟩

/-- Directional surface area is invariant under rotation. -/
lemma directionalSurfaceArea_transfer (p : MvPolynomial (Fin 3) ℝ)
    (R : Point 3 ≃ₗᵢ[ℝ] Point 3) (e : Point 3) (hRe : R e = e3)
    (S : Set (Point 3)) :
    directionalSurfaceArea e p S =
    directionalSurfaceArea e3 (rotatedPoly p R) (R '' S) := by
  let p' := rotatedPoly p R
  let μ : Measure (Point 3) := Measure.hausdorffMeasure 2
  let g : Point 3 → ENNReal := fun y =>
    ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p' y)‖
  let f : Point 3 → ENNReal := fun x =>
    ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖
  let e_iso : Point 3 ≃ᵢ Point 3 :=
    { toFun := R
      invFun := R.symm
      left_inv := R.left_inv
      right_inv := R.right_inv
      isometry_toFun := LinearIsometryEquiv.isometry R }
  have h_mp : MeasurePreserving R μ μ := by
    have h := IsometryEquiv.measurePreserving_hausdorffMeasure e_iso (2 : ℝ)
    exact h
  have h_integrand : ∀ x : Point 3, g (R x) = f x := by
    intro x
    have h1 : polynomialUnitNormal p' (R x) = R (polynomialUnitNormal p x) :=
      rotatedPoly_unitNormal p R x
    dsimp only [g, f]
    rw [h1]
    have h2 : inner ℝ e3 (R (polynomialUnitNormal p x)) =
        inner ℝ (R.symm e3) (polynomialUnitNormal p x) := by
      have h3 := linearIsometryEquiv_preserves_inner R (R.symm e3) (polynomialUnitNormal p x)
      have h4 : R (R.symm e3) = e3 := R.apply_symm_apply e3
      rw [h4] at h3
      exact h3
    rw [h2]
    have h4 : R.symm e3 = e := by
      have h5 : R e = e3 := hRe
      have h6 : R.symm (R e) = e := R.left_inv e
      rw [h5] at h6
      exact h6
    rw [h4]
  have h_main : ∫⁻ y in R '' S, g y ∂μ = ∫⁻ x in S, f x ∂μ := by
    classical
    have h_mp_restrict : MeasurePreserving R (μ.restrict S) (μ.restrict (R '' S)) := by
      have h_map : Measure.map R (μ.restrict S) = μ.restrict (R '' S) := by
        ext T hT
        have h1 : Measure.map R (μ.restrict S) T = (μ.restrict S) (R ⁻¹' T) := by
          rw [Measure.map_apply R.continuous.measurable hT]
        rw [h1]
        have hRinv : MeasurableSet (R ⁻¹' T) := R.continuous.measurable hT
        have h_left : (μ.restrict S) (R ⁻¹' T) = μ (R ⁻¹' T ∩ S) := by
          exact Measure.restrict_apply hRinv
        have h_right : (μ.restrict (R '' S)) T = μ (T ∩ R '' S) := by
          exact Measure.restrict_apply hT
        rw [h_left, h_right]
        have h_set : R '' (R ⁻¹' T ∩ S) = T ∩ R '' S := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨y, ⟨hyT, hyS⟩, rfl⟩
            exact ⟨hyT, y, hyS, rfl⟩
          · rintro ⟨hzT, y, hyS, rfl⟩
            exact ⟨y, ⟨hzT, hyS⟩, rfl⟩
        have h_image : μ (R '' (R ⁻¹' T ∩ S)) = μ (R ⁻¹' T ∩ S) :=
          linearIsometryEquiv_preserves_hausdorffMeasure R (R ⁻¹' T ∩ S)
        have h_eq : μ (R ⁻¹' T ∩ S) = μ (T ∩ R '' S) := by
          rw [h_set] at h_image
          exact h_image.symm
        exact h_eq
      exact ⟨R.continuous.measurable, h_map⟩
    let h_measEquiv : Point 3 ≃ᵐ Point 3 :=
      { R with
        measurable_toFun := R.continuous.measurable
        measurable_invFun := R.symm.continuous.measurable }
    have h_map2 : ∫⁻ y, g y ∂(μ.restrict (R '' S)) = ∫⁻ x, g (R x) ∂(μ.restrict S) :=
      MeasureTheory.MeasurePreserving.lintegral_map_equiv g h_measEquiv h_mp_restrict
    have h3 : ∫⁻ x, g (R x) ∂(μ.restrict S) = ∫⁻ x, f x ∂(μ.restrict S) := by
      congr with x
      exact h_integrand x
    rw [h_map2, h3]
  have h_final : directionalSurfaceArea e p S = directionalSurfaceArea e3 (rotatedPoly p R) (R '' S) := by
    dsimp only [directionalSurfaceArea, f, g]
    exact h_main.symm
  exact h_final

end Kakeya.CV
