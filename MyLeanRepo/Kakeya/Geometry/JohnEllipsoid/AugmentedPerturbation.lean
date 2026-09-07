import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Perturbation
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Separation
import Mathlib.Tactic


noncomputable section

open MeasureTheory
open scoped Pointwise Real MatrixOrder

namespace JohnEllipsoid

variable {n : ℕ}

/-- inner product on E n equals the sum of component products. -/
lemma inner_eq_sum (u v : E n) : inner ℝ u v = ∑ i : Fin n, u i * v i := by
  have h_norm2 : ∀ (w : E n), ‖w‖ ^ 2 = ∑ i : Fin n, w i ^ 2 := by
    intro w
    have h1 : quadForm (1 : Matrix (Fin n) (Fin n) ℝ) w = ‖w‖ ^ 2 := quadForm_one w
    have h2 : quadForm (1 : Matrix (Fin n) (Fin n) ℝ) w = ∑ i : Fin n, w i ^ 2 := by
      simp [quadForm, Matrix.one_apply, Finset.sum_ite, Finset.mem_univ, if_true]
      have h3 : ∑ i : Fin n, w i * w i = ∑ i : Fin n, w i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      exact h3
    linarith
  have h_polar : inner ℝ u v = (‖u + v‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2) / 2 := by
    have h : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_add_sq_real u v
    linarith
  rw [h_polar]
  rw [h_norm2 (u + v), h_norm2 u, h_norm2 v]
  have h4 : ∑ i : Fin n, (u + v) i ^ 2 = ∑ i : Fin n, (u i ^ 2 + 2 * u i * v i + v i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    have h5 : (u + v) i = u i + v i := by simp
    rw [h5] <;> ring
  rw [h4]
  have h5 : ∑ i : Fin n, (u i ^ 2 + 2 * u i * v i + v i ^ 2) =
      (∑ i : Fin n, u i ^ 2) + 2 * (∑ i : Fin n, u i * v i) + (∑ i : Fin n, v i ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    <;> ring_nf
  rw [h5] <;> ring

/-- Bilinear form associated with matrix P: B(u,v) = sum_{ij} u_i P_{ij} v_j. -/
def bilinForm (P : Matrix (Fin n) (Fin n) ℝ) (u v : E n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, u i * P i j * v j

lemma bilinForm_add_left (P : Matrix (Fin n) (Fin n) ℝ) (u1 u2 v : E n) :
    bilinForm P (u1 + u2) v = bilinForm P u1 v + bilinForm P u2 v := by
  simp only [bilinForm]
  have h : ∀ (i : Fin n), ∑ j : Fin n, (u1 + u2) i * P i j * v j =
      (∑ j : Fin n, u1 i * P i j * v j) + (∑ j : Fin n, u2 i * P i j * v j) := by
    intro i
    have h2 : (u1 + u2) i = u1 i + u2 i := by simp
    rw [h2]
    have h3 : ∑ j : Fin n, (u1 i + u2 i) * P i j * v j =
        ∑ j : Fin n, (u1 i * P i j * v j + u2 i * P i j * v j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h3, Finset.sum_add_distrib]
  calc
    ∑ i, ∑ j, (u1 + u2) i * P i j * v j
      = ∑ i, ((∑ j, u1 i * P i j * v j) + (∑ j, u2 i * P i j * v j)) := by
        apply Finset.sum_congr rfl; intro i _; exact h i
    _ = (∑ i, ∑ j, u1 i * P i j * v j) + (∑ i, ∑ j, u2 i * P i j * v j) := by
        rw [Finset.sum_add_distrib]

lemma bilinForm_add_right (P : Matrix (Fin n) (Fin n) ℝ) (u v1 v2 : E n) :
    bilinForm P u (v1 + v2) = bilinForm P u v1 + bilinForm P u v2 := by
  simp only [bilinForm]
  have h : ∀ (i : Fin n), ∑ j : Fin n, u i * P i j * (v1 + v2) j =
      (∑ j : Fin n, u i * P i j * v1 j) + (∑ j : Fin n, u i * P i j * v2 j) := by
    intro i
    have h2 : ∀ j, (v1 + v2) j = v1 j + v2 j := by intro j; simp
    have h3 : ∑ j : Fin n, u i * P i j * (v1 + v2) j =
        ∑ j : Fin n, (u i * P i j * v1 j + u i * P i j * v2 j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h2 j] <;> ring
    rw [h3, Finset.sum_add_distrib]
  calc
    ∑ i, ∑ j, u i * P i j * (v1 + v2) j
      = ∑ i, ((∑ j, u i * P i j * v1 j) + (∑ j, u i * P i j * v2 j)) := by
        apply Finset.sum_congr rfl; intro i _; exact h i
    _ = (∑ i, ∑ j, u i * P i j * v1 j) + (∑ i, ∑ j, u i * P i j * v2 j) := by
        rw [Finset.sum_add_distrib]

/-- For symmetric P, the associated linear map is self-adjoint. -/
lemma toLpLin_self_adjoint (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm) (u v : E n) :
    inner ℝ (P.toLpLin 2 2 u) v = inner ℝ u (P.toLpLin 2 2 v) := by
  rw [inner_eq_sum (P.toLpLin 2 2 u) v, inner_eq_sum u (P.toLpLin 2 2 v)]
  have h1 : ∑ i : Fin n, (P.toLpLin 2 2 u) i * v i =
           ∑ i : Fin n, ∑ j : Fin n, v i * P i j * u j := by
    apply Finset.sum_congr rfl
    intro i _
    have h2 : (P.toLpLin 2 2 u) i = ∑ j : Fin n, P i j * u j := by rfl
    rw [h2, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h3 : ∑ i : Fin n, u i * (P.toLpLin 2 2 v) i =
           ∑ i : Fin n, ∑ j : Fin n, u i * P i j * v j := by
    apply Finset.sum_congr rfl
    intro i _
    have h4 : (P.toLpLin 2 2 v) i = ∑ j : Fin n, P i j * v j := by rfl
    rw [h4, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h3]
  have h4 : ∑ i : Fin n, ∑ j : Fin n, v i * P i j * u j =
           ∑ j : Fin n, ∑ i : Fin n, v i * P i j * u j := by
    rw [Finset.sum_comm]
  rw [h4]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hT : P i j = P j i := by
    have hT1 : P.transpose = P := hP
    calc P i j = P.transpose j i := by simp [Matrix.transpose_apply]
      _ = P j i := by rw [hT1]
  rw [hT] <;> ring

lemma bilinForm_eq_inner (P : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    bilinForm P u v = inner ℝ (P.toLpLin 2 2 v) u := by
  have h1 : bilinForm P u v = ∑ i : Fin n, u i * (P.toLpLin 2 2 v) i := by
    simp only [bilinForm]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : (P.toLpLin 2 2 v) i = ∑ j : Fin n, P i j * v j := by rfl
    have h3 : u i * (P.toLpLin 2 2 v) i = ∑ j : Fin n, u i * P i j * v j := by
      rw [h2]
      have h4 : u i * (∑ j : Fin n, P i j * v j) = ∑ j : Fin n, u i * (P i j * v j) := by
        rw [Finset.mul_sum] <;> rfl
      rw [h4]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact h3.symm
  rw [h1, inner_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bilinForm_symm (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm) (u v : E n) :
    bilinForm P u v = bilinForm P v u := by
  have h1 : bilinForm P u v = inner ℝ (P.toLpLin 2 2 v) u := bilinForm_eq_inner P u v
  have h2 : bilinForm P v u = inner ℝ (P.toLpLin 2 2 u) v := bilinForm_eq_inner P v u
  rw [h1, h2]
  have h3 : inner ℝ (P.toLpLin 2 2 v) u = inner ℝ u (P.toLpLin 2 2 v) := real_inner_comm _ _
  rw [h3]
  exact (toLpLin_self_adjoint P hP u v).symm

lemma quadForm_eq_bilinForm (P : Matrix (Fin n) (Fin n) ℝ) (u : E n) :
    quadForm P u = bilinForm P u u := by rfl

/-- For symmetric P, quadForm expansion. -/
lemma quadForm_add_symm (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm) (x d : E n) :
    quadForm P (x + d) = quadForm P x + 2 * inner ℝ (P.toLpLin 2 2 d) x + quadForm P d := by
  have h1 : quadForm P (x + d) = bilinForm P (x + d) (x + d) := by rfl
  rw [h1]
  have h2 : bilinForm P (x + d) (x + d) =
      bilinForm P x x + bilinForm P x d + bilinForm P d x + bilinForm P d d := by
    rw [bilinForm_add_left, bilinForm_add_right, bilinForm_add_right] <;> ring
  rw [h2]
  have h3 : bilinForm P d x = bilinForm P x d := bilinForm_symm P hP d x
  rw [h3]
  have h5 : bilinForm P x d = inner ℝ (P.toLpLin 2 2 d) x := bilinForm_eq_inner P x d
  rw [h5]
  have h6 : bilinForm P x x = quadForm P x := by rfl
  have h7 : bilinForm P d d = quadForm P d := by rfl
  rw [h6, h7] <;> ring

/-- Completing the square for PD P:
    `quadForm P x + 2*inner(b,x) = quadForm P (x + P⁻¹b) - quadForm P (P⁻¹b)`. -/
lemma completing_square (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (x b : E n) :
    quadForm P x + 2 * inner ℝ b x =
    quadForm P (x + P⁻¹.toLpLin 2 2 b) - quadForm P (P⁻¹.toLpLin 2 2 b) := by
  let d := P⁻¹.toLpLin 2 2 b
  have hdet : P.det ≠ 0 := hP.det_pos.ne'
  have hPd : P.toLpLin 2 2 d = b := by
    simp only [d]
    have h : (P.toLpLin 2 2) ((P⁻¹.toLpLin 2 2) b) = ((P * P⁻¹).toLpLin 2 2) b := by
      rw [Matrix.toLpLin_mul_same] <;> rfl
    rw [h]
    have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (Ne.isUnit hdet)
    rw [h2] <;> simp
  have hM_symm : P.IsSymm := hP.posSemidef.1
  have h_expand := quadForm_add_symm P hM_symm x d
  have h_inner : inner ℝ (P.toLpLin 2 2 d) x = inner ℝ b x := by rw [hPd]
  rw [h_expand, h_inner] <;> ring

/-- Given K compact, K ⊆ B(0,1), symmetric M, vector b, α, and for all u ∈ K with ‖u‖=1:
    quadForm M u + 2 inner(b,u) < α, then ∃ ε > 0 such that for 0 < t < ε:
    K ⊆ {x | quadForm (1+t•M) x + 2*t*inner(b,x) ≤ 1+t*α}. -/
lemma K_subset_augmented_perturbation {K : Set (E n)} (hK : IsCompact K)
    (hK_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (b : E n) (α : ℝ)
    (h_contact : ∀ u ∈ K, ‖u‖ = 1 → quadForm M u + 2 * inner ℝ b u < α) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε →
      K ⊆ {x : E n | quadForm (1 + t • M) x + 2 * t * inner ℝ b x ≤ 1 + t * α} := by
  let f : E n → ℝ := fun x => 1 - ‖x‖ ^ 2
  let g : E n → ℝ := fun x => α - quadForm M x - 2 * inner ℝ b x
  have hf_cont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hg_cont : Continuous g := by
    have h1 : Continuous (fun x : E n => quadForm M x) := quadForm_continuous M
    have h2 : Continuous (fun x : E n => inner ℝ b x) := by fun_prop
    have h3 : Continuous (fun x : E n => 2 * inner ℝ b x) := h2.const_mul 2
    have h4 : Continuous (fun x : E n => quadForm M x + 2 * inner ℝ b x) := h1.add h3
    have h5 : Continuous (fun x : E n => α - (quadForm M x + 2 * inner ℝ b x)) := continuous_const.sub h4
    have h6 : ∀ (x : E n), (α - (quadForm M x + 2 * inner ℝ b x)) = g x := by
      intro x; simp [g] <;> ring
    exact h5.congr h6
  have hf_nonneg : ∀ x ∈ K, 0 ≤ f x := by
    intro x hx
    have h : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hK_sub hx
    dsimp only [f]
    nlinarith [norm_nonneg x]
  have hg_pos : ∀ x ∈ K, f x = 0 → 0 < g x := by
    intro x hx hfx
    have h_norm : ‖x‖ = 1 := by
      dsimp only [f] at hfx
      have h : ‖x‖ ^ 2 = 1 := by linarith
      have h' : 0 ≤ ‖x‖ := by positivity
      nlinarith
    have h : quadForm M x + 2 * inner ℝ b x < α := h_contact x hx h_norm
    dsimp only [g]
    linarith
  rcases positive_perturbation hK hf_cont hg_cont hf_nonneg hg_pos with ⟨ε, hε, hpos⟩
  refine ⟨ε, hε, fun t ht_pos ht_lt => ?_⟩
  intro x hx
  have h : 0 < f x + t * g x := hpos t ht_pos ht_lt x hx
  dsimp only [f, g] at h
  have h_quad : quadForm (1 + t • M) x = ‖x‖ ^ 2 + t * quadForm M x := by
    have h1 : quadForm (1 + t • M) x = quadForm (1 : Matrix (Fin n) (Fin n) ℝ) x + t * quadForm M x := by
      rw [quadForm_add, quadForm_smul] <;> ring
    rw [h1, quadForm_one]
  have h_goal : quadForm (1 + t • M) x + 2 * t * inner ℝ b x ≤ 1 + t * α := by
    rw [h_quad]
    linarith
  simpa [Set.mem_setOf_eq] using h_goal

/-- Volume comparison for augmented perturbation: if `n*α - trace(M) < 0`, then for sufficiently
    small `t > 0`, the augmented perturbed ellipsoid has smaller volume than the unit ball. -/
lemma augmented_perturbation_volume_less (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (b : E n) (α : ℝ) (h : (n : ℝ) * α - M.trace < 0) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε,
      let P := 1 + t • M
      let d_t := t • (P⁻¹.toLpLin 2 2 b)
      let r_t := 1 + t * α + t ^ 2 * quadForm P (P⁻¹.toLpLin 2 2 b)
      P.PosDef ∧ 0 < r_t ∧
      ∃ (c_t : E n) (A_t : E n ≃ₗ[ℝ] E n),
        {x : E n | quadForm P x + 2 * t * inner ℝ b x ≤ 1 + t * α} = ellipsoid c_t A_t ∧
        0 < LinearMap.det (A_t : E n →ₗ[ℝ] E n) ∧
        LinearMap.det (A_t : E n →ₗ[ℝ] E n) < 1 := by
  -- Step 1: Positive definiteness of P = 1 + t•M for small t
  rcases posDef_I_tM M hM with ⟨ε1, hε1, hPD⟩
  -- Step 2: Define P(t), q(t), and show q continuous at 0
  let P_t : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => 1 + t • M
  let q : ℝ → ℝ := fun t => quadForm (P_t t) ((P_t t)⁻¹.toLpLin 2 2 b)
  have hP_cont : Continuous P_t := by fun_prop
  have hdet0 : (P_t 0).det ≠ 0 := by simp [P_t]
  -- q(t) is continuous at 0 because matrix inverse is continuous at invertible matrices
  have hq_cont : ContinuousAt q 0 := by
    -- Matrix inverse continuity via adjugate formula
    have h_adj_cont : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) := by fun_prop
    have h_det_cont : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by fun_prop
    have h_inv_formula : ∀ (A : Matrix (Fin n) (Fin n) ℝ), A.det ≠ 0 →
        A⁻¹ = (A.det)⁻¹ • A.adjugate := by
      intro A hA
      let B := (A.det)⁻¹ • A.adjugate
      have h1 : A * A.adjugate = A.det • 1 := Matrix.mul_adjugate A
      have h1' : A.adjugate * A = A.det • 1 := Matrix.adjugate_mul A
      have h_step1 : A * B = (A.det)⁻¹ • (A * A.adjugate) := by
        simp [B, Matrix.mul_smul] <;> rfl
      have h_step2 : B * A = (A.det)⁻¹ • (A.adjugate * A) := by
        simp [B, Matrix.smul_mul] <;> rfl
      have hAB : A * B = 1 := by
        rw [h_step1, h1]
        simp [smul_smul, hA] <;> field_simp [hA] <;> rfl
      have hBA : B * A = 1 := by
        rw [h_step2, h1']
        simp [smul_smul, hA] <;> field_simp [hA] <;> rfl
      have hA' : IsUnit A.det := by simpa [isUnit_iff_ne_zero] using hA
      have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA'
      have h_eq : B = A⁻¹ := by
        calc B
          = B * 1 := by simp
        _ = B * (A * A⁻¹) := by rw [hAAinv]
        _ = (B * A) * A⁻¹ := by rw [Matrix.mul_assoc]
        _ = 1 * A⁻¹ := by rw [hBA]
        _ = A⁻¹ := by simp
      exact h_eq.symm
    have h1 : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => (A.det)⁻¹ • A.adjugate) (P_t 0) := by
      fun_prop
    have h_ev : ∀ᶠ (A : Matrix (Fin n) (Fin n) ℝ) in nhds (P_t 0), A.det ≠ 0 :=
      h_det_cont.continuousAt.eventually_ne hdet0
    have h_inv_cont : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) (P_t 0) :=
      h1.congr_of_eventuallyEq (h_ev.mono fun A hA => h_inv_formula A hA)
    have h_mat_inv_cont : ContinuousAt (fun t : ℝ => (P_t t)⁻¹) 0 :=
      h_inv_cont.comp hP_cont.continuousAt
    -- Helper: finite sum of ContinuousAt functions is ContinuousAt (specialized to ℝ)
    have h_sum_at : ∀ (s : Finset (Fin n)) (f : (Fin n) → ℝ → ℝ)
        (h : ∀ k ∈ s, ContinuousAt (f k) 0),
        ContinuousAt (fun t : ℝ => ∑ k ∈ s, f k t) 0 := by
      intro s f h
      induction s using Finset.induction with
      | empty => simpa using continuousAt_const
      | @insert k s hk ih =>
        have h_eq : (fun t : ℝ => ∑ x ∈ insert k s, f x t) = fun t => f k t + ∑ x ∈ s, f x t := by
          funext t
          rw [Finset.sum_insert hk]
        rw [h_eq]
        exact (h k (Finset.mem_insert_self k s)).add
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    -- Each entry of the inverse matrix is continuous at 0
    have h_inv_entry : ∀ (i k : Fin n), ContinuousAt (fun t : ℝ => (P_t t)⁻¹ i k) 0 := by
      intro i k
      have h1 : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A i k) := by fun_prop
      exact h1.continuousAt.comp h_mat_inv_cont
    -- Each component of v(t) = (P_t t)⁻¹.toLpLin 2 2 b is continuous at 0
    have h_v_component : ∀ (i : Fin n), ContinuousAt (fun t : ℝ => ((P_t t)⁻¹.toLpLin 2 2 b) i) 0 := by
      intro i
      have h_eq : (fun t : ℝ => ((P_t t)⁻¹.toLpLin 2 2 b) i) =
          fun t : ℝ => ∑ k : Fin n, (P_t t)⁻¹ i k * b k := by
        funext t; rfl
      rw [h_eq]
      have h : ∀ k ∈ (Finset.univ : Finset (Fin n)), ContinuousAt (fun t : ℝ => (P_t t)⁻¹ i k * b k) 0 := by
        intro k _
        exact (h_inv_entry i k).mul continuous_const.continuousAt
      exact h_sum_at Finset.univ (fun k t => (P_t t)⁻¹ i k * b k) h
    -- Each entry of P(t) is continuous at 0
    have h_P_entry : ∀ (i j : Fin n), ContinuousAt (fun t : ℝ => (P_t t) i j) 0 := by
      intro i j
      have h1 : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) := by fun_prop
      exact h1.continuousAt.comp hP_cont.continuousAt
    -- Each term in quadForm is continuous at 0
    have h_term : ∀ (i j : Fin n), ContinuousAt (fun t : ℝ =>
        ((P_t t)⁻¹.toLpLin 2 2 b) i * (P_t t) i j * ((P_t t)⁻¹.toLpLin 2 2 b) j) 0 := by
      intro i j
      have h_ab : ContinuousAt (fun t : ℝ => ((P_t t)⁻¹.toLpLin 2 2 b) i * (P_t t) i j) 0 :=
        (h_v_component i).mul (h_P_entry i j)
      have h_goal : (fun t : ℝ => ((P_t t)⁻¹.toLpLin 2 2 b) i * (P_t t) i j * ((P_t t)⁻¹.toLpLin 2 2 b) j) =
          fun t : ℝ => (((P_t t)⁻¹.toLpLin 2 2 b) i * (P_t t) i j) * ((P_t t)⁻¹.toLpLin 2 2 b) j := by
        funext t; ring
      rw [h_goal]
      exact h_ab.mul (h_v_component j)
    -- The double sum is continuous at 0
    let term : (Fin n) → (Fin n) → ℝ → ℝ := fun i j t =>
      ((P_t t)⁻¹.toLpLin 2 2 b) i * (P_t t) i j * ((P_t t)⁻¹.toLpLin 2 2 b) j
    have h_inner_sum : ∀ (i : Fin n), ContinuousAt (fun t : ℝ => ∑ j : Fin n, term i j t) 0 := by
      intro i
      have h : ∀ j ∈ (Finset.univ : Finset (Fin n)), ContinuousAt (term i j) 0 := by
        intro j _
        exact h_term i j
      exact h_sum_at Finset.univ (term i) h
    have h_outer : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ContinuousAt (fun t : ℝ => ∑ j : Fin n, term i j t) 0 := by
      intro i _
      exact h_inner_sum i
    have h_sum : ContinuousAt (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n, term i j t) 0 :=
      h_sum_at Finset.univ (fun i t => ∑ j : Fin n, term i j t) h_outer
    have h_q_eq : q = fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n, term i j t := by
      funext t
      simp only [q, quadForm, term] <;> rfl
    rw [h_q_eq]
    exact h_sum
  -- Step 3: Define r(t) and show HasDerivAt r α 0
  let r : ℝ → ℝ := fun t => 1 + t * α + t ^ 2 * q t
  have hr0 : r 0 = 1 := by simp [r, q, P_t] <;> norm_num
  have h_deriv_t2q : HasDerivAt (fun t : ℝ => t ^ 2 * q t) 0 0 := by
    have h_q_bdd : (fun t : ℝ => q t) =O[nhds 0] (fun _ : ℝ => (1 : ℝ)) := by
      exact Filter.Tendsto.isBigO_one ℝ hq_cont
    have h_t_o_1 : (fun t : ℝ => t) =o[nhds 0] (fun _ : ℝ => (1 : ℝ)) := by
      exact (Asymptotics.isLittleO_one_iff ℝ).mpr fun ⦃U⦄ hU => hU
    have h_t_O_t : (fun t : ℝ => t) =O[nhds 0] (fun t : ℝ => t) := by
      exact Asymptotics.isBigO_refl (fun t => t) (nhds 0)
    have h_t2_o_t1 : (fun t : ℝ => t * t) =o[nhds 0] (fun t : ℝ => 1 * t) :=
      h_t_o_1.mul_isBigO h_t_O_t
    have h_t2_o_t : (fun t : ℝ => t ^ 2) =o[nhds 0] (fun t : ℝ => t) := by
      have h1 : (fun t : ℝ => t * t) = (fun t : ℝ => t ^ 2) := by funext t; ring
      have h2 : (fun t : ℝ => 1 * t) = (fun t : ℝ => t) := by funext t; ring
      rw [h1, h2] at h_t2_o_t1
      exact h_t2_o_t1
    have h_mul1 : (fun t : ℝ => t ^ 2 * q t) =o[nhds 0] (fun t : ℝ => t * (1 : ℝ)) :=
      h_t2_o_t.mul_isBigO h_q_bdd
    have h_mul2 : (fun t : ℝ => t ^ 2 * q t) =o[nhds 0] (fun t : ℝ => t) := by
      have h3 : (fun t : ℝ => t * (1 : ℝ)) = (fun t : ℝ => t) := by funext t; ring
      rw [h3] at h_mul1
      exact h_mul1
    have h_main : (fun t : ℝ => t ^ 2 * q t - (0 : ℝ)) =o[nhds 0] (fun t : ℝ => t - (0 : ℝ)) := by
      simpa using h_mul2
    simpa [hasDerivAt_iff_isLittleO] using h_main
  have h_deriv_r : HasDerivAt r α 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * α) α 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const α
    have h2 : HasDerivAt (fun t : ℝ => (t * α) + 1) α 0 := h1.add_const 1
    have h3 : (fun t : ℝ => 1 + t * α) = (fun t : ℝ => (t * α) + 1) := by funext t; ring
    have h1' : HasDerivAt (fun t : ℝ => 1 + t * α) α 0 := by
      rw [h3] at *
      <;> exact h2
    have h4 : HasDerivAt (fun t : ℝ => t ^ 2 * q t) 0 0 := h_deriv_t2q
    have h5 : r = fun t : ℝ => (1 + t * α) + t ^ 2 * q t := by funext t; rfl
    rw [h5]
    have h6 : HasDerivAt (fun t : ℝ => (1 + t * α) + t ^ 2 * q t) (α + 0) 0 := h1'.add h4
    have h7 : α + 0 = α := by ring
    rw [h7] at h6
    exact h6
  -- Step 4: Derivative of log(r(t))
  have h_deriv_logr : HasDerivAt (fun t : ℝ => Real.log (r t)) α 0 := by
    have h_main : HasDerivAt (fun t : ℝ => Real.log (r t)) (α / r 0) 0 :=
      h_deriv_r.log (by rw [hr0] <;> norm_num)
    have h_simp : α / r 0 = α := by rw [hr0] <;> ring
    rw [h_simp] at h_main
    exact h_main
  -- Step 5: Derivative of log(det P(t))
  have h_deriv_det := det_log_deriv_at_zero M
  -- Step 6: Define f(t) and show negative derivative
  let f : ℝ → ℝ := fun t =>
    ((n : ℝ) / 2) * Real.log (r t) - (1 / 2 : ℝ) * Real.log (Matrix.det (P_t t))
  have h_f0 : f 0 = 0 := by
    simp [f, r, q, P_t, hr0] <;> norm_num
  set c1 : ℝ := (n : ℝ) / 2 with hc1
  set c2 : ℝ := (1 / 2 : ℝ) with hc2
  have h1 : HasDerivAt (fun t : ℝ => c1 * Real.log (r t)) (c1 * α) 0 :=
    h_deriv_logr.const_mul c1
  have h2 : HasDerivAt (fun t : ℝ => c2 * Real.log (Matrix.det (P_t t))) (c2 * M.trace) 0 :=
    h_deriv_det.const_mul c2
  have h_deriv_f : HasDerivAt f (c1 * α - c2 * M.trace) 0 := h1.sub h2
  have h_deriv_val : c1 * α - c2 * M.trace = c2 * ((n : ℝ) * α - M.trace) := by
    simp [hc1, hc2] <;> ring
  rw [h_deriv_val] at h_deriv_f
  have h_neg : c2 * ((n : ℝ) * α - M.trace) < 0 := by
    have h5 : (n : ℝ) * α - M.trace < 0 := h
    simp [hc2] <;> linarith
  let g : ℝ → ℝ := fun t => -f t
  have h_g0 : g 0 = 0 := by simp [g, h_f0] <;> ring
  have h_deriv_g : HasDerivAt g (-(c2 * ((n : ℝ) * α - M.trace))) 0 := h_deriv_f.neg
  have h_pos_deriv : 0 < -(c2 * ((n : ℝ) * α - M.trace)) := by
    simp [hc2] <;> linarith
  rcases small_t_exists g (-(c2 * ((n : ℝ) * α - M.trace))) h_pos_deriv h_deriv_g h_g0
    with ⟨ε2, hε2, hpos⟩
  -- Step 7: r(t) > 0 for small t
  have h_r_pos : ∃ ε3 > 0, ∀ t ∈ Set.Ioo 0 ε3, 0 < r t := by
    have h_cont : ContinuousAt r 0 := h_deriv_r.continuousAt
    have h_pos0 : 0 < r 0 := by rw [hr0] <;> norm_num
    have h_eventually : ∀ᶠ t in nhds 0, 0 < r t :=
      h_cont.eventually (Ioi_mem_nhds h_pos0)
    rcases Metric.mem_nhds_iff.mp h_eventually with ⟨ε3, hε3, h3⟩
    refine ⟨ε3, hε3, fun t ht => ?_⟩
    have h4 : dist t 0 < ε3 := by
      simpa [Real.dist_eq, abs_lt] using ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact h3 (by simpa [Real.dist_eq] using h4)
  rcases h_r_pos with ⟨ε3, hε3, hr_pos⟩
  -- Step 8: Combine epsilon bounds
  let ε := min ε1 (min ε2 ε3)
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h_t1 : t ∈ Set.Ioo 0 ε1 := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have h_t2 : t ∈ Set.Ioo 0 ε2 := ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have h_t3 : t ∈ Set.Ioo 0 ε3 := ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hPD_t : (P_t t).PosDef := hPD t h_t1.1 h_t1.2
  have hr_pos_t : 0 < r t := hr_pos t h_t3
  have h_f_neg : f t < 0 := by
    have h6 : 0 < g t := hpos t h_t2
    simpa [g] using h6
  -- Step 9: Complete the square and build ellipsoid
  let P := P_t t
  let d_t := t • (P⁻¹.toLpLin 2 2 b)
  let r_t := r t
  have hdet_t : P.det ≠ 0 := hPD_t.det_pos.ne'
  have h_square : ∀ (x : E n), quadForm P x + 2 * t * inner ℝ b x =
      quadForm P (x + d_t) - t ^ 2 * quadForm P (P⁻¹.toLpLin 2 2 b) := by
    intro x
    have h_scale := completing_square P hPD_t x (t • b)
    have h7 : P⁻¹.toLpLin 2 2 (t • b) = d_t := by
      simp [d_t] <;> rfl
    rw [h7] at h_scale
    have h8 : inner ℝ (t • b) x = t * inner ℝ b x := by
      rw [inner_smul_left]
      <;> simp [starRingEnd]
      <;> ring
    rw [h8] at h_scale
    have h9 : quadForm P d_t = t ^ 2 * quadForm P (P⁻¹.toLpLin 2 2 b) := by
      have h10 : d_t = t • (P⁻¹.toLpLin 2 2 b) := by rfl
      rw [h10]
      simp [quadForm, map_smul, Finset.mul_sum]
      <;> ring_nf
    rw [h9] at h_scale
    linarith
  have h_set_eq : {x : E n | quadForm P x + 2 * t * inner ℝ b x ≤ 1 + t * α} =
      {x : E n | quadForm P (x + d_t) ≤ r_t} := by
    ext x
    have h10 := h_square x
    simp only [Set.mem_setOf_eq]
    rw [h10]
    <;> dsimp only [r_t, r] <;> constructor <;> intro h <;> linarith
  have h_translate : {x : E n | quadForm P (x + d_t) ≤ r_t} =
      (-d_t) +ᵥ {y : E n | quadForm P y ≤ r_t} := by
    ext x
    simp only [Set.mem_vadd_set, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨x + d_t, h, ?_⟩
      simp [vadd_eq_add] <;> abel
    · rintro ⟨y, hy, rfl⟩
      simpa [vadd_eq_add] using hy
  rcases ellipsoid_of_quadForm P hPD_t hr_pos_t with ⟨A_t, h_ellipsoid, h_det_A⟩
  let c_t := -d_t
  have h_ellipsoid0 : ellipsoid (0 : E n) A_t = A_t '' Metric.closedBall (0 : E n) 1 := by
    simp [ellipsoid]
    <;> rfl
  have h_final_set : {x : E n | quadForm P x + 2 * t * inner ℝ b x ≤ 1 + t * α} = ellipsoid c_t A_t := by
    rw [h_set_eq, h_translate, h_ellipsoid, h_ellipsoid0]
    <;> simp [c_t, ellipsoid]
    <;> rfl
  have h_det_pos : 0 < LinearMap.det (A_t : E n →ₗ[ℝ] E n) := by
    rw [h_det_A]
    have h_num_pos : 0 < (Real.sqrt r_t) ^ n := by positivity
    have h_den_pos : 0 < Real.sqrt (Matrix.det P) := by
      have h10 : 0 < Matrix.det P := hPD_t.det_pos
      exact Real.sqrt_pos.mpr h10
    exact div_pos h_num_pos h_den_pos
  have h_log_det : Real.log (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) = f t := by
    rw [h_det_A]
    have h7 : Real.log ((Real.sqrt r_t) ^ n / Real.sqrt (Matrix.det P)) =
        (n : ℝ) / 2 * Real.log r_t - (1 / 2 : ℝ) * Real.log (Matrix.det P) := by
      have h8 : 0 < Real.sqrt r_t := Real.sqrt_pos.mpr hr_pos_t
      have h9 : 0 < Real.sqrt (Matrix.det P) := by
        have h10 : 0 < Matrix.det P := hPD_t.det_pos
        exact Real.sqrt_pos.mpr h10
      have h10 : Real.log ((Real.sqrt r_t) ^ n) = (n : ℝ) / 2 * Real.log r_t := by
        rw [Real.log_pow]
        have h11 : Real.log (Real.sqrt r_t) = (1 / 2 : ℝ) * Real.log r_t := by
          rw [Real.log_sqrt (by linarith [hr_pos_t])] <;> ring
        rw [h11] <;> ring
      have h12 : Real.log ((Real.sqrt r_t) ^ n / Real.sqrt (Matrix.det P)) =
          Real.log ((Real.sqrt r_t) ^ n) - Real.log (Real.sqrt (Matrix.det P)) :=
        Real.log_div (ne_of_gt (by positivity)) (ne_of_gt h9)
      rw [h12, h10]
      have h13 : Real.log (Real.sqrt (Matrix.det P)) = (1 / 2 : ℝ) * Real.log (Matrix.det P) := by
        rw [Real.log_sqrt (by linarith [hPD_t.det_pos])] <;> ring
      rw [h13] <;> ring
    exact h7
  have h_final : LinearMap.det (A_t : E n →ₗ[ℝ] E n) < 1 := by
    have h13 : Real.log (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) < 0 := by
      rw [h_log_det] <;> exact h_f_neg
    have h14 : 0 < LinearMap.det (A_t : E n →ₗ[ℝ] E n) := h_det_pos
    have h15 : Real.log (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) < Real.log 1 := by
      simpa using h13
    exact (Real.log_lt_log_iff h14 (by norm_num)).mp h15
  exact ⟨hPD_t, hr_pos_t, c_t, A_t, h_final_set, h_det_pos, h_final⟩

end JohnEllipsoid
