import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.IneqUtils
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Order

noncomputable section

open JohnEllipsoid MeasureTheory
open scoped Pointwise Real MatrixOrder

namespace JohnEllipsoid

variable {n : ℕ}

/-- Quadratic form x^T M x for a real matrix. -/
def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (x : E n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j

lemma quadForm_one (x : E n) : quadForm (1 : Matrix (Fin n) (Fin n) ℝ) x = ‖x‖ ^ 2 := by
  have h1 : ∀ (i : Fin n), ∑ j : Fin n, x i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * x j = x i ^ 2 := by
    intro i
    simp [Matrix.one_apply, Finset.sum_ite, Finset.mem_univ, if_true]
    <;> ring
  have h2 : quadForm (1 : Matrix (Fin n) (Fin n) ℝ) x = ∑ i : Fin n, (x i) ^ 2 := by
    rw [quadForm]
    apply Finset.sum_congr rfl
    intro i _
    exact h1 i
  rw [h2]
  have h3 : ∑ i : Fin n, (x i) ^ 2 ≥ 0 := by positivity
  have h4 : ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2) := by
    simp [EuclideanSpace.norm_eq]
    <;> rfl
  rw [h4]
  rw [Real.sq_sqrt h3]

lemma quadForm_add (M N : Matrix (Fin n) (Fin n) ℝ) (x : E n) :
    quadForm (M + N) x = quadForm M x + quadForm N x := by
  simp only [quadForm, Matrix.add_apply]
  have h : ∀ (i : Fin n), ∑ j : Fin n, x i * (M i j + N i j) * x j =
      (∑ j : Fin n, x i * M i j * x j) + (∑ j : Fin n, x i * N i j * x j) := by
    intro i
    have h2 : ∑ j : Fin n, x i * (M i j + N i j) * x j =
        ∑ j : Fin n, (x i * M i j * x j + x i * N i j * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h2, Finset.sum_add_distrib]
  calc
    ∑ i, ∑ j, x i * (M i j + N i j) * x j
      = ∑ i, ((∑ j, x i * M i j * x j) + (∑ j, x i * N i j * x j)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
    _ = (∑ i, ∑ j, x i * M i j * x j) + (∑ i, ∑ j, x i * N i j * x j) := by
        rw [Finset.sum_add_distrib]

lemma quadForm_smul (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : E n) :
    quadForm (t • M) x = t * quadForm M x := by
  simp only [quadForm, Matrix.smul_apply]
  have h : ∑ i : Fin n, ∑ j : Fin n, x i * (t * M i j) * x j =
      t * ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
    have h2 : ∀ (i : Fin n), ∑ j : Fin n, x i * (t * M i j) * x j =
        t * ∑ j : Fin n, x i * M i j * x j := by
      intro i
      have h3 : ∑ j : Fin n, x i * (t * M i j) * x j =
          ∑ j : Fin n, t * (x i * M i j * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h3, Finset.mul_sum]
    calc
      ∑ i, ∑ j, x i * (t * M i j) * x j
        = ∑ i, (t * ∑ j, x i * M i j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h2 i
      _ = t * ∑ i, ∑ j, x i * M i j * x j := by
          rw [Finset.mul_sum]
  exact h

lemma quadForm_continuous (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x : E n => quadForm M x) := by
  have h1 : ∀ (i j : Fin n), Continuous (fun x : E n => x i * M i j * x j) := by
    intro i j
    fun_prop
  have h2 : ∀ (i : Fin n), Continuous (fun x : E n => ∑ j : Fin n, x i * M i j * x j) := by
    intro i
    have h3 : Continuous (fun x : E n => ∑ j ∈ Finset.univ, x i * M i j * x j) := by
      exact continuous_list_sum (List.finRange n) fun j _ => h1 i j
    simpa using h3
  have h4 : Continuous (fun x : E n => ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, x i * M i j * x j) := by
    exact continuous_list_sum (List.finRange n) fun i _ => h2 i
  simpa [quadForm] using h4

/-- General perturbation lemma: if K is compact in a T2Space, f ≥ 0 on K, and g > 0 wherever f = 0 on K,
then for sufficiently small t > 0, f(x) + t*g(x) > 0 for all x ∈ K. -/
lemma positive_perturbation {X : Type*} [TopologicalSpace X] [T2Space X] {K : Set X}
    (hK : IsCompact K) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf_nonneg : ∀ x ∈ K, 0 ≤ f x)
    (hg_pos : ∀ x ∈ K, f x = 0 → 0 < g x) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε → ∀ x ∈ K, 0 < f x + t * g x := by
  let Z : Set X := {x | f x = 0}
  have hZ_closed : IsClosed Z := isClosed_singleton.preimage hf
  let S : Set X := K ∩ Z
  have hS_compact : IsCompact S := hK.inter_right hZ_closed
  have hg_bdd : ∃ C, ∀ x ∈ K, |g x| ≤ C := by
    have h1 : BddAbove (g '' K) := hK.bddAbove_image hg.continuousOn
    have h2 : BddBelow (g '' K) := hK.bddBelow_image hg.continuousOn
    rcases h1 with ⟨C1, hC1⟩
    rcases h2 with ⟨C2, hC2⟩
    let C := max C1 (-C2)
    refine ⟨C, fun x hx => ?_⟩
    have h3 : g x ∈ g '' K := ⟨x, hx, rfl⟩
    have h4 : g x ≤ C1 := hC1 h3
    have h5 : C2 ≤ g x := hC2 h3
    have h6 : g x ≤ C := by
      calc g x ≤ C1 := h4
           _ ≤ max C1 (-C2) := le_max_left _ _
    have h7 : -g x ≤ C := by
      calc -g x ≤ -C2 := by linarith
           _ ≤ max C1 (-C2) := le_max_right _ _
    rw [abs_le]
    constructor <;> linarith
  rcases hg_bdd with ⟨C, hC⟩
  by_cases hS_empty : S = ∅
  · -- S empty: f > 0 on K
    by_cases hK_empty : K = ∅
    · exact ⟨1, by norm_num, fun t _ _ => by rw [hK_empty] <;> simp⟩
    · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
      have h_main : ∃ x0 ∈ K, ∀ x ∈ K, f x0 ≤ f x :=
        hK.exists_isMinOn hK_nonempty hf.continuousOn
      rcases h_main with ⟨x0, hx0, hmin⟩
      have h_f0_pos : 0 < f x0 := by
        by_contra h
        have h4 : f x0 = 0 := by linarith [hf_nonneg x0 hx0]
        have h5 : x0 ∈ S := by exact ⟨hx0, h4⟩
        rw [hS_empty] at h5
        simpa using h5
      let η := f x0
      have hη_pos : 0 < η := h_f0_pos
      by_cases hC0 : C = 0
      · exact ⟨1, by norm_num, fun t _ _ x hx => by
          have h6 : f x ≥ η := hmin x hx
          have h7 : g x = 0 := by
            have h8 : |g x| ≤ C := hC x hx
            rw [hC0] at h8
            have h9 : |g x| ≤ 0 := h8
            have h10 : |g x| ≥ 0 := abs_nonneg _
            have h11 : |g x| = 0 := by linarith
            exact abs_eq_zero.mp h11
          rw [h7]
          have h12 : f x > 0 := by linarith
          linarith⟩
      · have hC_pos : 0 < C := by
          by_contra h
          have h' : C ≤ 0 := by linarith
          have h'' : |g x0| ≤ C := hC x0 hx0
          have h_pos : 0 ≤ |g x0| := abs_nonneg _
          have h_eq : C = 0 := by linarith
          exact hC0 h_eq
        let ε := η / C
        have hε_pos : 0 < ε := div_pos hη_pos hC_pos
        exact ⟨ε, hε_pos, fun t ht_pos ht_lt x hx => by
          have h5 : f x ≥ η := hmin x hx
          have h6 : |g x| ≤ C := hC x hx
          have h7 : g x ≥ -C := (abs_le.mp h6).1
          have h9 : t * C < η := by
            have h10 : t < η / C := ht_lt
            have h11 : t * C < (η / C) * C := by gcongr
            have h12 : (η / C) * C = η := by
              field_simp [hC_pos.ne'] <;> ring
            rw [h12] at h11
            exact h11
          have h13 : η - t * C > 0 := by linarith
          have h14 : t * g x ≥ -t * C := by
            have h15 : t > 0 := ht_pos
            nlinarith
          have h16 : f x + t * g x ≥ η - t * C := by linarith
          linarith⟩
  · -- S nonempty
    have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    have h_min_g_S : ∃ x0 ∈ S, ∀ x ∈ S, g x0 ≤ g x :=
      hS_compact.exists_isMinOn hS_nonempty hg.continuousOn
    rcases h_min_g_S with ⟨x0, hx0S, hmin_g⟩
    have h_g0_pos : 0 < g x0 := hg_pos x0 hx0S.1 hx0S.2
    let δ := g x0
    have hδ_pos : 0 < δ := h_g0_pos
    let U : Set X := g ⁻¹' Set.Ioi (δ / 2)
    have hU_open : IsOpen U := isOpen_Ioi.preimage hg
    have hS_sub_U : S ⊆ U := by
      intro x hx
      have h1 : δ ≤ g x := hmin_g x hx
      have h2 : δ / 2 < g x := by linarith
      exact h2
    let KminU : Set X := K \ U
    have hUc_closed : IsClosed (Uᶜ) := hU_open.isClosed_compl
    have hKminU_compact : IsCompact KminU := hK.inter_right hUc_closed
    have hf_pos_on_KminU : ∀ x ∈ KminU, 0 < f x := by
      intro x hx
      have h1 : x ∈ K := hx.1
      have h2 : x ∉ U := hx.2
      by_contra h3
      have h4 : f x = 0 := by linarith [hf_nonneg x h1]
      have h5 : x ∈ S := ⟨h1, h4⟩
      have h6 : x ∈ U := hS_sub_U h5
      exact h2 h6
    by_cases hKminU_empty : KminU = ∅
    · exact ⟨1, by norm_num, fun t ht_pos _ x hx => by
        have h_xU : x ∈ U := by
          by_contra h
          have h' : x ∈ KminU := ⟨hx, h⟩
          rw [hKminU_empty] at h'
          simpa using h'
        have h_ih : δ / 2 < g x := h_xU
        have h8 : 0 ≤ f x := hf_nonneg x hx
        have h9 : 0 < g x := by linarith
        have h10 : 0 < t * g x := mul_pos ht_pos h9
        linarith⟩
    · have hKminU_nonempty : KminU.Nonempty := Set.nonempty_iff_ne_empty.mpr hKminU_empty
      have h_min_f : ∃ y0 ∈ KminU, ∀ x ∈ KminU, f y0 ≤ f x :=
        hKminU_compact.exists_isMinOn hKminU_nonempty hf.continuousOn
      rcases h_min_f with ⟨y0, hy0, hmin_f⟩
      let η := f y0
      have hη_pos : 0 < η := hf_pos_on_KminU y0 hy0
      have hC_pos : 0 < C := by
        have h1 : 0 < g x0 := h_g0_pos
        have h2 : |g x0| ≤ C := hC x0 hx0S.1
        have h3 : 0 < |g x0| := abs_pos.mpr h1.ne'
        linarith
      let ε := η / C
      have hε_pos : 0 < ε := div_pos hη_pos hC_pos
      exact ⟨ε, hε_pos, fun t ht_pos ht_lt x hx => by
        by_cases h_xU : x ∈ U
        · have h_ih : δ / 2 < g x := h_xU
          have h8 : 0 ≤ f x := hf_nonneg x hx
          have h9 : 0 < g x := by linarith
          have h10 : 0 < t * g x := mul_pos ht_pos h9
          linarith
        · have h_xKminU : x ∈ KminU := ⟨hx, h_xU⟩
          have h5 : f x ≥ η := hmin_f x h_xKminU
          have h6 : |g x| ≤ C := hC x hx
          have h7 : g x ≥ -C := (abs_le.mp h6).1
          have h9 : t * C < η := by
            have h10 : t < η / C := ht_lt
            have h11 : t * C < (η / C) * C := by gcongr
            have h12 : (η / C) * C = η := by
              field_simp [hC_pos.ne'] <;> ring
            rw [h12] at h11
            exact h11
          have h13 : η - t * C > 0 := by linarith
          have h14 : t * g x ≥ -t * C := by
            have h15 : t > 0 := ht_pos
            nlinarith
          have h16 : f x + t * g x ≥ η - t * C := by linarith
          linarith⟩

/-- The set E_t = {x : x^T(I+tM)x ≤ 1+tα}. -/
def perturbationEllipsoid (M : Matrix (Fin n) (Fin n) ℝ) (α t : ℝ) : Set (E n) :=
  {x | quadForm (1 + t • M) x ≤ 1 + t * α}

/-- If K ⊆ closedBall 0 1 is compact, and quadForm M u < α for all u ∈ K with ‖u‖ = 1,
then K ⊆ perturbationEllipsoid M α t for all sufficiently small t > 0. -/
lemma K_subset_perturbation (K : Set (E n))
    (hK_compact : IsCompact K)
    (hK_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ)
    (hS_strict : ∀ u ∈ K, ‖u‖ = 1 → quadForm M u < α) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε → K ⊆ perturbationEllipsoid M α t := by
  let f : E n → ℝ := fun x => 1 - ‖x‖ ^ 2
  let g : E n → ℝ := fun x => α - quadForm M x
  have hf_cont : Continuous f := by fun_prop
  have hg_cont : Continuous g := by
    have h : Continuous (fun x : E n => quadForm M x) := quadForm_continuous M
    exact continuous_const.sub h
  have hf_nonneg : ∀ x ∈ K, 0 ≤ f x := by
    intro x hx
    have h1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hK_sub hx
    have h2 : ‖x‖ ^ 2 ≤ 1 := by
      have h3 : 0 ≤ ‖x‖ := by positivity
      nlinarith
    dsimp only [f]
    linarith
  have hg_pos : ∀ x ∈ K, f x = 0 → 0 < g x := by
    intro x hx hfx
    have h_norm1 : ‖x‖ ^ 2 = 1 := by
      dsimp only [f] at hfx
      linarith
    have h_norm : ‖x‖ = 1 := by
      have h_pos : 0 ≤ ‖x‖ := by positivity
      nlinarith
    have h : quadForm M x < α := hS_strict x hx h_norm
    dsimp only [g]
    linarith
  have h_main := positive_perturbation hK_compact hf_cont hg_cont hf_nonneg hg_pos
  rcases h_main with ⟨ε, hε_pos, h⟩
  refine ⟨ε, hε_pos, fun t ht_pos ht_lt => ?_⟩
  intro x hx
  have h_pos : 0 < f x + t * g x := h t ht_pos ht_lt x hx
  have h9 : quadForm (1 + t • M) x ≤ 1 + t * α := by
    have h10 : quadForm (1 + t • M) x = ‖x‖ ^ 2 + t * quadForm M x := by
      calc
        quadForm (1 + t • M) x
          = quadForm (1 : Matrix (Fin n) (Fin n) ℝ) x + quadForm (t • M) x := quadForm_add 1 (t • M) x
        _ = ‖x‖ ^ 2 + quadForm (t • M) x := by rw [quadForm_one]
        _ = ‖x‖ ^ 2 + t * quadForm M x := by rw [quadForm_smul]
    rw [h10]
    dsimp only [f, g] at h_pos
    linarith
  exact h9

/-- Quadratic form for ordinary functions. -/
def quadFormFn (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j

/-- Helper: ∑ i, f i * c = (∑ i, f i) * c. -/
private lemma sum_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    ∑ i : α, f i * c = (∑ i : α, f i) * c := by
  exact Eq.symm (Finset.sum_mul Finset.univ f c)

/-- Bound on quadratic form: |quadFormFn M x| ≤ (∑ i,j, |M i j|) * (∑ i, (x i)^2). -/
lemma quadFormFn_abs_bound (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    |quadFormFn M x| ≤ (∑ i : Fin n, ∑ j : Fin n, |M i j|) * (∑ i : Fin n, (x i)^2) := by
  let C := ∑ i : Fin n, ∑ j : Fin n, |M i j|
  let N := ∑ i : Fin n, (x i)^2
  have hN_nonneg : 0 ≤ N := by positivity
  have h1 : |quadFormFn M x| ≤ ∑ i : Fin n, ∑ j : Fin n, |x i * M i j * x j| := by
    calc
      |quadFormFn M x|
        = |∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j| := by rfl
      _ ≤ ∑ i : Fin n, |∑ j : Fin n, x i * M i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |x i * M i j * x j| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
  have h_xi_sq : ∀ i, (x i)^2 ≤ N := by
    intro i
    apply Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∀ i j, |x i * M i j * x j| ≤ |M i j| * N := by
    intro i j
    have h3 : |x i * M i j * x j| = |x i| * |M i j| * |x j| := by
      have h4 : |x i * M i j * x j| = |x i| * |M i j| * |x j| := by
        calc
          |x i * M i j * x j|
            = |(x i * M i j) * x j| := by rfl
          _ = |x i * M i j| * |x j| := by rw [abs_mul]
          _ = |x i| * |M i j| * |x j| := by rw [abs_mul] <;> ring
      exact h4
    rw [h3]
    have h5 : |x i| ≤ Real.sqrt N := by
      have h6 : (x i)^2 ≤ N := h_xi_sq i
      have h7 : |x i| = Real.sqrt ((x i)^2) := by
        rw [← Real.sqrt_sq (show 0 ≤ |x i| from abs_nonneg _)] <;> simp
      rw [h7]
      gcongr
    have h6 : |x j| ≤ Real.sqrt N := by
      have h7 : (x j)^2 ≤ N := h_xi_sq j
      have h8 : |x j| = Real.sqrt ((x j)^2) := by
        rw [← Real.sqrt_sq (show 0 ≤ |x j| from abs_nonneg _)] <;> simp
      rw [h8]
      gcongr
    have h7 : |x i| * |x j| ≤ Real.sqrt N * Real.sqrt N := by gcongr
    have h8 : Real.sqrt N * Real.sqrt N = N := by
      have h9 : Real.sqrt N * Real.sqrt N = (Real.sqrt N)^2 := by ring
      rw [h9, Real.sq_sqrt hN_nonneg]
    rw [h8] at h7
    have h_goal : |x i| * |M i j| * |x j| ≤ |M i j| * N := by
      calc
        |x i| * |M i j| * |x j| = |M i j| * (|x i| * |x j|) := by ring
        _ ≤ |M i j| * N := by gcongr
    exact h_goal
  have h3 : ∑ i : Fin n, ∑ j : Fin n, |x i * M i j * x j| ≤ C * N := by
    have h41 : ∑ i : Fin n, ∑ j : Fin n, |x i * M i j * x j| ≤ ∑ i : Fin n, ∑ j : Fin n, (|M i j| * N) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact h2 i j
    have h42 : ∑ i : Fin n, ∑ j : Fin n, (|M i j| * N) = C * N := by
      have h5 : ∑ i : Fin n, ∑ j : Fin n, (|M i j| * N) = ∑ i : Fin n, ((∑ j : Fin n, |M i j|) * N) := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_mul_const (fun j => |M i j|) N
      rw [h5]
      have h8 : ∑ i : Fin n, ((∑ j : Fin n, |M i j|) * N) = (∑ i : Fin n, ∑ j : Fin n, |M i j|) * N := by
        exact sum_mul_const (fun i => ∑ j : Fin n, |M i j|) N
      rw [h8]
      <;> rfl
    rw [h42] at h41
    exact h41
  exact le_trans h1 h3

/-- quadFormFn (1) x = ∑ i, (x i)^2. -/
lemma quadFormFn_one (x : Fin n → ℝ) :
    quadFormFn (1 : Matrix (Fin n) (Fin n) ℝ) x = ∑ i : Fin n, (x i)^2 := by
  have h : ∀ (i : Fin n), ∑ j : Fin n, x i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * x j = (x i)^2 := by
    intro i
    simp [Matrix.one_apply, Finset.sum_ite, Finset.mem_univ, if_true]
    <;> ring
  have h2 : quadFormFn (1 : Matrix (Fin n) (Fin n) ℝ) x = ∑ i : Fin n, (x i)^2 := by
    rw [quadFormFn]
    apply Finset.sum_congr rfl
    intro i _
    exact h i
  exact h2

/-- quadFormFn (t • M) x = t * quadFormFn M x. -/
lemma quadFormFn_smul (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    quadFormFn (t • M) x = t * quadFormFn M x := by
  have h : ∀ (i : Fin n), ∑ j : Fin n, x i * (t • M) i j * x j = t * ∑ j : Fin n, x i * M i j * x j := by
    intro i
    have h2 : ∑ j : Fin n, x i * (t • M) i j * x j = ∑ j : Fin n, t * (x i * M i j * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [Matrix.smul_apply] <;> ring
    rw [h2, Finset.mul_sum]
  rw [quadFormFn]
  have h_outer : ∑ i : Fin n, ∑ j : Fin n, x i * (t • M) i j * x j =
      ∑ i : Fin n, (t * ∑ j : Fin n, x i * M i j * x j) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h i
  have h_final : ∑ i : Fin n, (t * ∑ j : Fin n, x i * M i j * x j) = t * ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
    rw [← Finset.mul_sum] <;> rfl
  rw [h_outer, h_final]
  <;> rfl

/-- quadFormFn (M + N) x = quadFormFn M x + quadFormFn N x. -/
lemma quadFormFn_add (M N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadFormFn (M + N) x = quadFormFn M x + quadFormFn N x := by
  have h : ∀ (i : Fin n), ∑ j : Fin n, x i * (M + N) i j * x j =
      (∑ j : Fin n, x i * M i j * x j) + (∑ j : Fin n, x i * N i j * x j) := by
    intro i
    have h2 : ∑ j : Fin n, x i * (M + N) i j * x j =
        ∑ j : Fin n, (x i * M i j * x j + x i * N i j * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [Matrix.add_apply] <;> ring
    rw [h2, Finset.sum_add_distrib]
  rw [quadFormFn, quadFormFn, quadFormFn]
  have h3 : ∑ i : Fin n, ∑ j : Fin n, x i * (M + N) i j * x j =
      ∑ i : Fin n, ((∑ j : Fin n, x i * M i j * x j) + (∑ j : Fin n, x i * N i j * x j)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h i
  rw [h3, Finset.sum_add_distrib]

/-- For symmetric M, I + t•M is positive definite for sufficiently small t > 0. -/
lemma posDef_I_tM (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    ∃ (t0 : ℝ), 0 < t0 ∧ ∀ t, 0 < t → t < t0 → (1 + t • M).PosDef := by
  let C := ∑ i : Fin n, ∑ j : Fin n, |M i j|
  by_cases hC : C = 0
  · have hM0 : M = 0 := by
      ext i j
      have h1 : 0 ≤ |M i j| := abs_nonneg _
      have h2 : |M i j| ≤ C := by
        have h3 : |M i j| ≤ ∑ j' : Fin n, |M i j'| := by
          apply Finset.single_le_sum (fun k _ => abs_nonneg _) (Finset.mem_univ j)
        have h4 : ∑ j' : Fin n, |M i j'| ≤ ∑ i' : Fin n, ∑ j' : Fin n, |M i' j'| := by
          apply Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
        linarith
      rw [hC] at h2
      have h5 : |M i j| = 0 := by linarith
      simpa [abs_eq_zero] using h5
    refine ⟨1, by norm_num, fun t _ _ => ?_⟩
    rw [hM0]
    simpa using Matrix.PosDef.one
  · have hC_pos : 0 < C := by
      have h' : 0 ≤ C := by positivity
      have h_ne : 0 ≠ C := by
        intro h
        exact hC (Eq.symm h)
      exact h'.lt_of_ne h_ne
    let t0 := 1 / C
    have ht0_pos : 0 < t0 := by positivity
    refine ⟨t0, ht0_pos, fun t ht_pos ht_lt => ?_⟩
    have h_tC : t * C < 1 := by
      have h : t < 1 / C := ht_lt
      have h' : t * C < (1 / C) * C := by gcongr
      have h'' : (1 / C) * C = 1 := by
        field_simp [hC_pos.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h_symm : (1 + t • M).IsSymm := by
      exact Matrix.isSymm_one.add (hM.smul t)
    have h_pos : ∀ (x : Fin n → ℝ), x ≠ 0 → 0 < quadFormFn (1 + t • M) x := by
      intro x hx
      set N := ∑ i : Fin n, (x i)^2 with hN_def
      have h_xi_sq : ∀ i, (x i)^2 ≤ N := by
        intro i
        rw [hN_def]
        apply Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      have hN_pos : 0 < N := by
        have hN_nonneg : 0 ≤ N := by positivity
        by_contra h
        have hN_le : N ≤ 0 := by linarith
        have hN_eq : N = 0 := le_antisymm hN_le hN_nonneg
        have h_all_zero : ∀ i, x i = 0 := by
          intro i
          have h2 : (x i)^2 ≤ N := h_xi_sq i
          rw [hN_eq] at h2
          have h3 : (x i)^2 ≤ 0 := h2
          have h4 : 0 ≤ (x i)^2 := by positivity
          have h5 : (x i)^2 = 0 := by exact le_antisymm h3 h4
          exact sq_eq_zero_iff.mp h5
        have hx0 : x = 0 := by
          funext i
          exact h_all_zero i
        exact hx hx0
      have h5 : quadFormFn (1 + t • M) x = N + t * quadFormFn M x := by
        calc
          quadFormFn (1 + t • M) x
            = quadFormFn (1 : Matrix (Fin n) (Fin n) ℝ) x + quadFormFn (t • M) x := quadFormFn_add 1 (t • M) x
          _ = N + quadFormFn (t • M) x := by rw [quadFormFn_one]
          _ = N + t * quadFormFn M x := by rw [quadFormFn_smul]
      rw [h5]
      have h7 : |quadFormFn M x| ≤ C * N := quadFormFn_abs_bound M x
      have h8 : -C * N ≤ quadFormFn M x := by
        have h9 : -|quadFormFn M x| ≤ quadFormFn M x := neg_abs_le (quadFormFn M x)
        have h10 : -C * N ≤ -|quadFormFn M x| := by linarith [h7]
        linarith
      have h11 : t * quadFormFn M x ≥ t * (-C * N) := by
        exact mul_le_mul_of_nonneg_left h8 (by linarith)
      have h12 : N + t * quadFormFn M x ≥ N - t * C * N := by linarith
      have h13 : N - t * C * N > 0 := by
        have h14 : 0 < N := hN_pos
        have h15 : 1 - t * C > 0 := by linarith
        have h16 : N - t * C * N = (1 - t * C) * N := by ring
        rw [h16]
        exact mul_pos h15 h14
      linarith
    have h_main : ∀ (x : Fin n → ℝ), x ≠ 0 → 0 < ∑ i, x i * (Matrix.mulVec (1 + t • M) x) i := by
      intro x hx
      have h9 : ∑ i : Fin n, x i * (Matrix.mulVec (1 + t • M) x) i =
          ∑ i : Fin n, x i * (∑ j : Fin n, (1 + t • M) i j * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      have h10 : ∑ i : Fin n, x i * (∑ j : Fin n, (1 + t • M) i j * x j) =
          ∑ i : Fin n, ∑ j : Fin n, x i * (1 + t • M) i j * x j := by
        apply Finset.sum_congr rfl
        intro i _
        have h11 : x i * (∑ j : Fin n, (1 + t • M) i j * x j) =
            ∑ j : Fin n, x i * ((1 + t • M) i j * x j) := by
          rw [Finset.mul_sum] <;> rfl
        rw [h11]
        apply Finset.sum_congr rfl
        intro j _
        <;> ring
      have h_eq : ∑ i : Fin n, x i * (Matrix.mulVec (1 + t • M) x) i = quadFormFn (1 + t • M) x := by
        rw [h9, h10]
        <;> rfl
      rw [h_eq]
      exact h_pos x hx
    have h_final : (1 + t • M).PosDef := by
      have h_goal : ∀ (x : Fin n → ℝ), x ≠ 0 → 0 < ∑ i : Fin n, (star (x i)) * (Matrix.mulVec (1 + t • M) x) i := by
        intro x hx
        have h_star : ∀ i, star (x i) = x i := by intro i; simp
        have h_dot : ∑ i : Fin n, (star (x i)) * (Matrix.mulVec (1 + t • M) x) i =
            ∑ i : Fin n, x i * (Matrix.mulVec (1 + t • M) x) i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_star i]
        rw [h_dot]
        exact h_main x hx
      exact Matrix.PosDef.of_dotProduct_mulVec_pos h_symm h_goal
    exact h_final

/-- For positive semidefinite P, quadFormFn P x = ∑ i, (Matrix.mulVec (CFC.sqrt P) x) i^2. -/
lemma quadFormFn_eq_sq_sqrt (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (x : Fin n → ℝ) :
    quadFormFn P x = ∑ i : Fin n, (Matrix.mulVec (CFC.sqrt P) x) i ^ 2 := by
  let B := CFC.sqrt P
  have hB_nonneg : 0 ≤ B := CFC.sqrt_nonneg P
  have hB_psd : B.PosSemidef := by
    have h : 0 ≤ B := hB_nonneg
    exact Matrix.LE.le.posSemidef hB_nonneg
  have hB_symm : B.IsSymm := hB_psd.isHermitian
  have hB2 : B * B = P := by
    have h : B ^ 2 = P := CFC.sq_sqrt P
    simpa [pow_two] using h
  have h1 : quadFormFn P x = ∑ i : Fin n, x i * (Matrix.mulVec P x) i := by
    have h2 : ∑ i : Fin n, x i * (Matrix.mulVec P x) i = ∑ i : Fin n, ∑ j : Fin n, x i * P i j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      have h3 : Matrix.mulVec P x i = ∑ j : Fin n, P i j * x j := by rfl
      rw [h3]
      have h4 : x i * (∑ j : Fin n, P i j * x j) = ∑ j : Fin n, x i * (P i j * x j) := by
        rw [Finset.mul_sum]
      rw [h4]
      apply Finset.sum_congr rfl
      intro j _
      <;> ring
    exact h2.symm
  rw [h1]
  have h5 : Matrix.mulVec P x = Matrix.mulVec B (Matrix.mulVec B x) := by
    have h51 : Matrix.mulVec (B * B) x = Matrix.mulVec B (Matrix.mulVec B x) := by
      exact Eq.symm (Matrix.mulVec_mulVec x B B)
    have h52 : P = B * B := hB2.symm
    rw [h52]
    exact h51
  have h6 : ∑ i : Fin n, x i * (Matrix.mulVec P x) i =
      ∑ i : Fin n, (Matrix.mulVec B x) i * (Matrix.mulVec B x) i := by
    rw [h5]
    have h_dot1 : (∑ i : Fin n, x i * (Matrix.mulVec B (Matrix.mulVec B x)) i) =
        x ⬝ᵥ (Matrix.mulVec B (Matrix.mulVec B x)) := by rfl
    rw [h_dot1]
    have h_dot2 : x ⬝ᵥ (Matrix.mulVec B (Matrix.mulVec B x)) =
        (Matrix.vecMul x B) ⬝ᵥ (Matrix.mulVec B x) :=
      Matrix.dotProduct_mulVec x B (Matrix.mulVec B x)
    rw [h_dot2]
    have h_vm : Matrix.vecMul x B = Matrix.mulVec B.transpose x := by
      ext i
      have h1 : Matrix.vecMul x B i = ∑ j : Fin n, x j * B j i := by rfl
      have h2 : Matrix.mulVec B.transpose x i = ∑ j : Fin n, B j i * x j := by rfl
      rw [h1, h2]
      apply Finset.sum_congr rfl
      intro j _
      <;> ring
    rw [h_vm]
    have h7 : B.transpose = B := hB_symm
    rw [h7]
    have h_final : (Matrix.mulVec B x) ⬝ᵥ (Matrix.mulVec B x) =
        ∑ i : Fin n, (Matrix.mulVec B x) i * (Matrix.mulVec B x) i := by
      simp [dotProduct]
      <;> rfl
    exact h_final
  rw [h6]
  have h9 : ∑ i : Fin n, (Matrix.mulVec B x) i * (Matrix.mulVec B x) i =
      ∑ i : Fin n, (Matrix.mulVec B x) i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    <;> ring
  rw [h9]

/-- Convert an invertible matrix to a linear equivalence on E n using toLpLin. -/
def matrixToLinEquiv (A : Matrix (Fin n) (Fin n) ℝ) (hdet : A.det ≠ 0) :
    E n ≃ₗ[ℝ] E n :=
  let hunit : IsUnit A.det := by
    exact Ne.isUnit hdet
  { toFun := A.toLpLin 2 2
    invFun := A⁻¹.toLpLin 2 2
    left_inv := by
      intro x
      have h : (A⁻¹.toLpLin 2 2) ((A.toLpLin 2 2) x) =
          ((A⁻¹ * A).toLpLin 2 2) x := by
        rw [Matrix.toLpLin_mul_same] <;> rfl
      rw [h]
      have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
      rw [h2]
      <;> simp
    right_inv := by
      intro y
      have h : (A.toLpLin 2 2) ((A⁻¹.toLpLin 2 2) y) =
          ((A * A⁻¹).toLpLin 2 2) y := by
        rw [Matrix.toLpLin_mul_same] <;> rfl
      rw [h]
      have h2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
      rw [h2]
      <;> simp
    map_add' := (A.toLpLin 2 2).map_add
    map_smul' := (A.toLpLin 2 2).map_smul }

/-- The determinant of matrixToLinEquiv equals the matrix determinant. -/
lemma matrixToLinEquiv_det (A : Matrix (Fin n) (Fin n) ℝ) (hdet : A.det ≠ 0) :
    LinearMap.det (matrixToLinEquiv A hdet : E n →ₗ[ℝ] E n) = A.det := by
  have h : (matrixToLinEquiv A hdet : E n →ₗ[ℝ] E n) = A.toLpLin 2 2 := by
    rfl
  rw [h]
  exact LinearMap.det_toLpLin 2 A

/-- For positive definite P, quadForm P x = ‖matrixToLinEquiv (CFC.sqrt P) x‖^2. -/
lemma quadForm_eq_norm_sqrt_linEquiv (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (x : E n) :
    let B := CFC.sqrt P
    let hdet : B.det ≠ 0 := by
      have h1 : 0 < P.det := hP.det_pos
      have h2 : B.det = RCLike.sqrt P.det := hP.posSemidef.det_sqrt
      have h3 : (RCLike.sqrt P.det : ℝ) = Real.sqrt P.det := by
        rw [RCLike.sqrt_of_nonneg (show 0 ≤ P.det from by linarith)] <;> simp
      rw [h2, h3]
      exact (Real.sqrt_pos.mpr h1).ne'
    quadForm P x = ‖matrixToLinEquiv B hdet x‖ ^ 2 := by
  dsimp only
  let B := CFC.sqrt P
  have hB_psd : B.PosSemidef := by
    have h : 0 ≤ B := CFC.sqrt_nonneg P
    exact Matrix.LE.le.posSemidef h
  have hdet : B.det ≠ 0 := by
    have h1 : 0 < P.det := hP.det_pos
    have h2 : B.det = RCLike.sqrt P.det := hP.posSemidef.det_sqrt
    have h3 : (RCLike.sqrt P.det : ℝ) = Real.sqrt P.det := by
      rw [RCLike.sqrt_of_nonneg (show 0 ≤ P.det from by linarith)] <;> simp
    rw [h2, h3]
    exact (Real.sqrt_pos.mpr h1).ne'
  let A_E := matrixToLinEquiv B hdet
  have h1 : quadForm P x = quadFormFn P x.ofLp := by
    simp [quadForm, quadFormFn]
    <;> rfl
  rw [h1]
  have h2 : quadFormFn P x.ofLp = ∑ i : Fin n, (Matrix.mulVec B x.ofLp) i ^ 2 :=
    quadFormFn_eq_sq_sqrt P hP.posSemidef x.ofLp
  rw [h2]
  have h3 : ‖A_E x‖ ^ 2 = ∑ i : Fin n, (A_E x) i ^ 2 := by
    have h4 : ‖A_E x‖ = Real.sqrt (∑ i : Fin n, (A_E x) i ^ 2) := by
      simp [EuclideanSpace.norm_eq] <;> rfl
    rw [h4]
    rw [Real.sq_sqrt (by positivity)]
  rw [h3]
  have h5 : ∀ i : Fin n, (A_E x) i = (Matrix.mulVec B x.ofLp) i := by
    intro i
    rfl
  apply Finset.sum_congr rfl
  intro i _
  exact congr_arg (fun y : ℝ => y ^ 2) (h5 i)

/-- A quadratic form sublevel set {x | quadForm P x ≤ r} is an ellipsoid centered at 0. -/
lemma ellipsoid_of_quadForm (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) {r : ℝ} (hr : 0 < r) :
    ∃ (A : E n ≃ₗ[ℝ] E n),
      {x : E n | quadForm P x ≤ r} = ellipsoid (0 : E n) A ∧
      LinearMap.det (A : E n →ₗ[ℝ] E n) = (Real.sqrt r) ^ n / Real.sqrt P.det := by
  let B := CFC.sqrt P
  have hB_psd : B.PosSemidef := by
    have h : 0 ≤ B := CFC.sqrt_nonneg P
    exact Matrix.LE.le.posSemidef h
  have hPdet_pos : 0 < P.det := hP.det_pos
  have hPdet_nonneg : 0 ≤ P.det := by linarith
  have hsqrt_eq : (RCLike.sqrt P.det : ℝ) = Real.sqrt P.det := by
    rw [RCLike.sqrt_of_nonneg hPdet_nonneg] <;> simp
  have hdet_B : B.det ≠ 0 := by
    have h2 : B.det = RCLike.sqrt P.det := hP.posSemidef.det_sqrt
    rw [h2, hsqrt_eq]
    exact (Real.sqrt_pos.mpr hPdet_pos).ne'
  let A_E := matrixToLinEquiv B hdet_B
  let sr : ℝ := Real.sqrt r
  have hsr_pos : 0 < sr := Real.sqrt_pos.mpr hr
  have hsr_ne_zero : sr ≠ 0 := hsr_pos.ne'
  let u : Units ℝ := Units.mk0 sr hsr_ne_zero
  let A : E n ≃ₗ[ℝ] E n := u • A_E.symm
  have hA_apply : ∀ (x : E n), A x = sr • A_E.symm x := by
    intro x; rfl
  have h_sr2 : sr ^ 2 = r := Real.sq_sqrt (by linarith)
  -- Set equality
  have h_set : {x : E n | quadForm P x ≤ r} = ellipsoid (0 : E n) A := by
    ext x
    have h_qf : quadForm P x = ‖A_E x‖ ^ 2 :=
      quadForm_eq_norm_sqrt_linEquiv P hP x
    simp only [Set.mem_setOf_eq, ellipsoid, Set.mem_vadd_set, Set.mem_image, zero_vadd]
    constructor
    · intro h
      have h6 : ‖A_E x‖ ≤ sr := by
        rw [h_qf] at h
        have h7 : ‖A_E x‖ ^ 2 ≤ r := h
        have h8 : 0 ≤ ‖A_E x‖ := by positivity
        nlinarith [h_sr2]
      let z := (sr⁻¹ : ℝ) • A_E x
      have hz_norm : ‖z‖ ≤ 1 := by
        have h10 : ‖z‖ = sr⁻¹ * ‖A_E x‖ := by
          rw [norm_smul] <;> simp [abs_of_pos hsr_pos] <;> ring
        rw [h10]
        have h11 : sr⁻¹ * ‖A_E x‖ ≤ 1 := by
          calc sr⁻¹ * ‖A_E x‖ ≤ sr⁻¹ * sr := by gcongr
            _ = 1 := by field_simp [hsr_ne_zero] <;> ring
        exact h11
      have hz_in : z ∈ Metric.closedBall (0 : E n) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz_norm
      have hA_z : A z = x := by
        have h13 : A z = sr • A_E.symm z := hA_apply z
        rw [h13]
        have h14 : A_E.symm z = (sr⁻¹ : ℝ) • A_E.symm (A_E x) := by
          simp [z, A_E.symm.map_smul] <;> rfl
        rw [h14]
        have h15 : A_E.symm (A_E x) = x := A_E.symm_apply_apply x
        rw [h15]
        rw [smul_smul]
        have h16 : sr * sr⁻¹ = 1 := by field_simp [hsr_ne_zero] <;> ring
        rw [h16, one_smul]
      exact ⟨z, hz_in, hA_z⟩
    · rintro ⟨z, hz, rfl⟩
      have hz1 : ‖z‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have h14 : A_E (A z) = sr • z := by
        have h15 : A z = sr • A_E.symm z := hA_apply z
        rw [h15]
        have h16 : A_E (sr • A_E.symm z) = sr • A_E (A_E.symm z) := by
          exact A_E.toLinearMap.map_smul sr (A_E.symm z)
        rw [h16]
        have h17 : A_E (A_E.symm z) = z := A_E.apply_symm_apply z
        rw [h17] <;> rfl
      have h18 : ‖A_E (A z)‖ = sr * ‖z‖ := by
        rw [h14, norm_smul] <;> simp [abs_of_pos hsr_pos] <;> ring
      have h19 : ‖A_E (A z)‖ ^ 2 ≤ r := by
        rw [h18]
        have h20 : sr * ‖z‖ ≤ sr := by
          have h21 : sr * ‖z‖ ≤ sr * 1 := mul_le_mul_of_nonneg_left hz1 hsr_pos.le
          rw [mul_one] at h21
          exact h21
        have h21 : (sr * ‖z‖) ^ 2 ≤ sr ^ 2 := by gcongr
        rw [h_sr2] at h21
        exact h21
      rw [h_qf]
      exact h19
  -- Determinant
  have h_det_A : LinearMap.det (A : E n →ₗ[ℝ] E n) = sr ^ n / Real.sqrt P.det := by
    have h1 : (A : E n →ₗ[ℝ] E n) = sr • (A_E.symm : E n →ₗ[ℝ] E n) := by
      ext y
      have h_u : (u : ℝ) = sr := by
        simp [u, Units.mk0]
        <;> rfl
      simp [A, h_u, hA_apply] <;> rfl
    rw [h1]
    have h_finrank : Module.finrank ℝ (E n) = n := by
      exact finrank_euclideanSpace_fin
    have h2 : LinearMap.det (sr • (A_E.symm : E n →ₗ[ℝ] E n)) =
        sr ^ n * LinearMap.det (A_E.symm : E n →ₗ[ℝ] E n) := by
      rw [LinearMap.det_smul, h_finrank] <;> rfl
    rw [h2]
    have h3 : LinearMap.det (A_E.symm : E n →ₗ[ℝ] E n) =
        (LinearMap.det (A_E : E n →ₗ[ℝ] E n))⁻¹ := by
      exact LinearEquiv.det_coe_symm A_E
    rw [h3]
    have h4 : LinearMap.det (A_E : E n →ₗ[ℝ] E n) = B.det := matrixToLinEquiv_det B hdet_B
    rw [h4]
    have h5 : B.det = RCLike.sqrt P.det := hP.posSemidef.det_sqrt
    rw [h5, hsqrt_eq]
    <;> field_simp [Real.sqrt_pos.mpr hPdet_pos] <;> ring
  exact ⟨A, h_set, h_det_A⟩

/-- Derivative of `Real.log (det (1 + t•M))` at `t = 0` is `trace M`. -/
lemma det_log_deriv_at_zero (M : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Matrix.det (1 + t • M))) M.trace 0 := by
  let M_poly : Matrix (Fin n) (Fin n) (Polynomial ℝ) := M.map Polynomial.C
  let X_mat : Matrix (Fin n) (Fin n) (Polynomial ℝ) := (Polynomial.X : Polynomial ℝ) • M_poly
  let one_mat : Matrix (Fin n) (Fin n) (Polynomial ℝ) := 1
  let p : Polynomial ℝ := Matrix.det (one_mat + X_mat)
  have h_eval : ∀ (t : ℝ), p.eval t = Matrix.det (1 + t • M) := by
    intro t
    have h1 : p.eval t = Matrix.det ((one_mat + X_mat).map (Polynomial.eval t)) := by
      let f : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom t
      have h_det_map : f ((one_mat + X_mat).det) =
          Matrix.det ((one_mat + X_mat).map f) := RingHom.map_det f (one_mat + X_mat)
      have h_f_eval : ∀ (p : Polynomial ℝ), f p = Polynomial.eval t p := by
        intro p; rfl
      have h_map : (one_mat + X_mat).map f = (one_mat + X_mat).map (Polynomial.eval t) := by
        ext i j; rfl
      rw [h_map] at h_det_map
      rw [h_f_eval] at h_det_map
      exact h_det_map
    rw [h1]
    have h2 : (one_mat + X_mat).map (Polynomial.eval t) = 1 + t • M := by
      ext i j
      simp [one_mat, X_mat, M_poly, Matrix.one_apply, Polynomial.eval_add,
        Polynomial.eval_smul, Polynomial.eval_C, Polynomial.eval_X]
      <;> split_ifs <;> simp [Polynomial.eval_zero] <;> ring
    rw [h2]
  have h_p0 : p.eval 0 = 1 := by
    rw [h_eval] <;> simp
  have h_deriv : (Polynomial.derivative p).eval 0 = M.trace :=
    Matrix.derivative_det_one_add_X_smul M
  have h1 : HasDerivAt (fun t : ℝ => p.eval t) ((Polynomial.derivative p).eval 0) 0 :=
    Polynomial.hasDerivAt p 0
  have h1' : HasDerivAt (fun t : ℝ => p.eval t) M.trace 0 := by
    rw [h_deriv] at h1
    exact h1
  have h_pos : 0 < p.eval 0 := by
    rw [h_p0] <;> norm_num
  have h_main : HasDerivAt (fun t : ℝ => Real.log (p.eval t)) (M.trace / p.eval 0) 0 :=
    h1'.log h_pos.ne'
  have h_eq : (fun t : ℝ => Real.log (p.eval t)) = fun t : ℝ => Real.log (Matrix.det (1 + t • M)) := by
    funext t
    rw [h_eval t]
  rw [h_eq] at h_main
  have h_final : M.trace / p.eval 0 = M.trace := by
    rw [h_p0] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- Volume comparison: if `n*α - trace(M) < 0`, then for sufficiently small `t > 0`,
the perturbed ellipsoid has smaller volume than the unit ball. -/
lemma perturbation_volume_less (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (α : ℝ) (h : (n : ℝ) * α - M.trace < 0) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε,
      let P := 1 + t • M
      let r := 1 + t * α
      P.PosDef ∧ 0 < r ∧
      ∃ (A : E n ≃ₗ[ℝ] E n),
        {x : E n | quadForm P x ≤ r} = ellipsoid (0 : E n) A ∧
        0 < LinearMap.det (A : E n →ₗ[ℝ] E n) ∧
        LinearMap.det (A : E n →ₗ[ℝ] E n) < 1 := by
  have h_deriv_det := det_log_deriv_at_zero M
  have h_deriv_log1 : HasDerivAt (fun t : ℝ => Real.log (1 + t * α)) α 0 := by
    have h_inner : HasDerivAt (fun t : ℝ => 1 + t * α) α 0 := by
      have h : HasDerivAt (fun t : ℝ => t * α) α 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const α
      have h_eq : (fun t : ℝ => 1 + t * α) = (fun t : ℝ => (t * α) + 1) := by funext t; ring
      rw [h_eq]
      exact h.add_const 1
    have h_main : HasDerivAt (fun t : ℝ => Real.log (1 + t * α)) (α / (1 + (0 : ℝ) * α)) 0 :=
      h_inner.log (by norm_num)
    have h_simp : α / (1 + (0 : ℝ) * α) = α := by ring
    rw [h_simp] at h_main
    exact h_main
  let f : ℝ → ℝ := fun (t : ℝ) =>
    ((n : ℝ) / 2) * Real.log (1 + t * α) - (1 / 2 : ℝ) * Real.log (Matrix.det (1 + t • M))
  have h_f0 : f 0 = 0 := by
    simp [f] <;> norm_num
  set c1 : ℝ := (n : ℝ) / 2 with hc1
  set c2 : ℝ := (1 / 2 : ℝ) with hc2
  have h1 : HasDerivAt (fun t : ℝ => c1 * Real.log (1 + t * α)) (c1 * α) 0 :=
    h_deriv_log1.const_mul c1
  have h2 : HasDerivAt (fun t : ℝ => c2 * Real.log (Matrix.det (1 + t • M))) (c2 * M.trace) 0 :=
    by exact h_deriv_det.const_mul c2
  have h_deriv_f : HasDerivAt f (c1 * α - c2 * M.trace) 0 :=
    h1.sub h2
  have h_deriv_val : c1 * α - c2 * M.trace = c2 * ((n : ℝ) * α - M.trace) := by
    simp [hc1, hc2] <;> ring
  rw [h_deriv_val] at h_deriv_f
  have h_neg : c2 * ((n : ℝ) * α - M.trace) < 0 := by
    have h5 : (n : ℝ) * α - M.trace < 0 := h
    simp [hc2] <;> linarith
  let g : ℝ → ℝ := fun t => -f t
  have h_g0 : g 0 = 0 := by
    simp [g, h_f0] <;> ring
  have h_deriv_g : HasDerivAt g (-(c2 * ((n : ℝ) * α - M.trace))) 0 :=
    h_deriv_f.neg
  have h_pos_deriv : 0 < -(c2 * ((n : ℝ) * α - M.trace)) := by
    simp [hc2] <;> linarith
  rcases small_t_exists g (-(c2 * ((n : ℝ) * α - M.trace))) h_pos_deriv h_deriv_g h_g0
    with ⟨ε1, hε1, hpos⟩
  rcases posDef_I_tM M hM with ⟨ε2, hε2, hPD⟩
  have h_r_pos : ∃ ε3 > 0, ∀ t ∈ Set.Ioo 0 ε3, 0 < 1 + t * α := by
    by_cases hα : α = 0
    · refine ⟨1, by norm_num, fun t _ => ?_⟩
      rw [hα] <;> norm_num
    · have h_cont : ContinuousAt (fun t : ℝ => 1 + t * α) 0 := by fun_prop
      have h_pos0 : 0 < (1 + (0 : ℝ) * α) := by norm_num
      have h_eventually : ∀ᶠ t in nhds 0, 0 < 1 + t * α :=
        h_cont.eventually (Ioi_mem_nhds h_pos0)
      rcases Metric.mem_nhds_iff.mp h_eventually with ⟨ε3, hε3, h3⟩
      refine ⟨ε3, hε3, fun t ht => ?_⟩
      have h4 : dist t 0 < ε3 := by
        simpa [Real.dist_eq, abs_lt] using ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact h3 (by simpa [Real.dist_eq] using h4)
  rcases h_r_pos with ⟨ε3, hε3, hr_pos⟩
  let ε := min ε1 (min ε2 ε3)
  have hε : 0 < ε := by positivity
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h_t1 : t ∈ Set.Ioo 0 ε1 := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have h_t2 : t ∈ Set.Ioo 0 ε2 := ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have h_t3 : t ∈ Set.Ioo 0 ε3 := ⟨ht.1, lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hPD_t : (1 + t • M).PosDef := hPD t h_t2.1 h_t2.2
  have hr_pos_t : 0 < 1 + t * α := hr_pos t h_t3
  have h_f_neg : f t < 0 := by
    have h6 : 0 < g t := hpos t h_t1
    simpa [g] using h6
  rcases ellipsoid_of_quadForm (1 + t • M) hPD_t hr_pos_t with ⟨A, h_set, h_det_A⟩
  have h_sqrt_pos : 0 < Real.sqrt (1 + t * α) := Real.sqrt_pos.mpr hr_pos_t
  have h_det_pos : 0 < LinearMap.det (A : E n →ₗ[ℝ] E n) := by
    rw [h_det_A]
    have h_num_pos : 0 < (Real.sqrt (1 + t * α)) ^ n := by positivity
    have h_den_pos : 0 < Real.sqrt (Matrix.det (1 + t • M)) := by
      have h10 : 0 < Matrix.det (1 + t • M) := hPD_t.det_pos
      exact Real.sqrt_pos.mpr h10
    exact div_pos h_num_pos h_den_pos
  have h_log_det : Real.log (LinearMap.det (A : E n →ₗ[ℝ] E n)) = f t := by
    rw [h_det_A]
    have h7 : Real.log ((Real.sqrt (1 + t * α)) ^ n / Real.sqrt (Matrix.det (1 + t • M))) =
        (n : ℝ) / 2 * Real.log (1 + t * α) - (1 / 2 : ℝ) * Real.log (Matrix.det (1 + t • M)) := by
      have h8 : 0 < Real.sqrt (1 + t * α) := h_sqrt_pos
      have h9 : 0 < Real.sqrt (Matrix.det (1 + t • M)) := by
        have h10 : 0 < Matrix.det (1 + t • M) := hPD_t.det_pos
        exact Real.sqrt_pos.mpr h10
      have h10 : Real.log ((Real.sqrt (1 + t * α)) ^ n) = (n : ℝ) / 2 * Real.log (1 + t * α) := by
        rw [Real.log_pow]
        have h11 : Real.log (Real.sqrt (1 + t * α)) = (1 / 2 : ℝ) * Real.log (1 + t * α) := by
          rw [Real.log_sqrt (by linarith)] <;> ring
        rw [h11] <;> ring
      have h8' : 0 < (Real.sqrt (1 + t * α)) ^ n := by positivity
      have h13 : Real.log ((Real.sqrt (1 + t * α)) ^ n / Real.sqrt (Matrix.det (1 + t • M))) =
          Real.log ((Real.sqrt (1 + t * α)) ^ n) - Real.log (Real.sqrt (Matrix.det (1 + t • M))) :=
        Real.log_div (ne_of_gt h8') (ne_of_gt h9)
      rw [h13, h10]
      have h12 : Real.log (Real.sqrt (Matrix.det (1 + t • M))) = (1 / 2 : ℝ) * Real.log (Matrix.det (1 + t • M)) := by
        rw [Real.log_sqrt (by linarith [hPD_t.det_pos])] <;> ring
      rw [h12] <;> ring
    exact h7
  have h_final : LinearMap.det (A : E n →ₗ[ℝ] E n) < 1 := by
    have h13 : Real.log (LinearMap.det (A : E n →ₗ[ℝ] E n)) < 0 := by
      rw [h_log_det] <;> exact h_f_neg
    have h14 : 0 < LinearMap.det (A : E n →ₗ[ℝ] E n) := h_det_pos
    have h15 : Real.log (LinearMap.det (A : E n →ₗ[ℝ] E n)) < Real.log 1 := by
      simpa using h13
    exact (Real.log_lt_log_iff h14 (by norm_num)).mp h15
  exact ⟨hPD_t, hr_pos_t, A, h_set, h_det_pos, h_final⟩

end JohnEllipsoid
