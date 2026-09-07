import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional


noncomputable section

open scoped Real InnerProductSpace

namespace JohnEllipsoid

/-! # Separation theorem for the Fritz John optimality condition

Works in `V := E(n) × ((Fin n × Fin n) → ℝ)` with the product norm.
A separating functional decomposes as `f(x, Y) = v·x + trace(M * Y)`,
with `M` symmetric, on symmetric inputs `Y`.
-/

/-- Matrix entries as a function on pairs. -/
abbrev MatrixEntries (n : ℕ) := (Fin n × Fin n) → ℝ

/-- The ambient product space for the Fritz John separation argument. -/
abbrev FritzJohnSpace (n : ℕ) := E n × MatrixEntries n

/-- Convert matrix entries to a Matrix. -/
def entriesToMatrix {n : ℕ} (M : MatrixEntries n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => M (i, j))

/-- The outer product `u ⊗ u` as matrix entries. -/
def outerProductEntries {n : ℕ} (u : E n) : MatrixEntries n :=
  fun p => u p.1 * u p.2

theorem outerProductEntries_symm {n : ℕ} (u : E n) :
    (entriesToMatrix (outerProductEntries u)).IsSymm := by
  ext i j
  simp [entriesToMatrix, outerProductEntries, Matrix.transpose_apply]
  <;> ring

theorem outerProductEntries_continuous {n : ℕ} :
    Continuous (outerProductEntries : E n → MatrixEntries n) := by
  apply continuous_pi
  intro p
  have h1 : Continuous (fun u : E n => u p.1) :=
    PiLp.continuous_apply 2 (fun x => ℝ) p.1
  have h2 : Continuous (fun u : E n => u p.2) :=
    PiLp.continuous_apply 2 (fun x => ℝ) p.2
  exact h1.mul h2

/-- Trace of product of two matrices given by entries: `trace(M * Y)`. -/
def traceMul {n : ℕ} (M Y : MatrixEntries n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, M (i, j) * Y (j, i)

/-- The contact set `{(u, u⊗u) : u ∈ K ∩ sphere 0 1}`. -/
def fjContactSet {n : ℕ} (K : Set (E n)) : Set (FritzJohnSpace n) :=
  (fun u : E n => (u, outerProductEntries u)) '' (K ∩ Metric.sphere (0 : E n) 1)

theorem fjContactSet_compact {n : ℕ} {K : Set (E n)}
    (hK_comp : IsCompact K) : IsCompact (fjContactSet K) := by
  have h_sphere_closed : IsClosed (Metric.sphere (0 : E n) 1) :=
    Metric.isClosed_sphere
  have h_inter_comp : IsCompact (K ∩ Metric.sphere (0 : E n) 1) :=
    hK_comp.inter_right h_sphere_closed
  have h_cont : Continuous (fun u : E n => (u, outerProductEntries u)) :=
    continuous_prodMk.mpr ⟨continuous_id, outerProductEntries_continuous⟩
  exact h_inter_comp.image h_cont


/-! ## Convex hull compactness in finite dimensions -/

/-- Helper: extend a convex combination indexed by `ι` to one indexed by `Fin N`,
using an embedding `e : ι ↪ Fin N` and padding with a base point `x0`. -/
private lemma extend_convex_combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {N : ℕ} (x0 : E) (hx0 : x0 ∈ s)
    {ι : Type*} [Fintype ι] (e : ι ↪ Fin N)
    (z : ι → E) (w : ι → ℝ)
    (hz_range : Set.range z ⊆ s) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    ∃ (w' : Fin N → ℝ) (z' : Fin N → E),
      (w' ∈ stdSimplex ℝ (Fin N)) ∧ (∀ j, z' j ∈ s) ∧
      (∑ j : Fin N, w' j • z' j = ∑ i : ι, w i • z i) := by
  let S : Finset (Fin N) := Finset.image e Finset.univ
  have h_inj : Set.InjOn e (↑(Finset.univ : Finset ι) : Set ι) := fun x _ y _ hxy => e.injective hxy
  let w' : Fin N → ℝ := fun j => ∑ i : ι, if e i = j then w i else 0
  let z' : Fin N → E := fun j =>
    if h : ∃ i : ι, e i = j then z (Classical.choose h) else x0
  have h_w'_at_e : ∀ i : ι, w' (e i) = w i := by
    intro i
    simp only [w']
    have h_goal : ∀ k ∈ Finset.univ, k ≠ i → (if e k = e i then w k else 0) = 0 := by
      intro k _ hki
      have h4 : e k ≠ e i := by intro h5; exact hki (e.injective h5)
      simp [h4]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) h_goal]
    simp
  have h_z'_at_e : ∀ i : ι, z' (e i) = z i := by
    intro i
    have h5 : ∃ i' : ι, e i' = e i := ⟨i, rfl⟩
    have h6 : Classical.choose h5 = i := by
      apply e.injective
      exact Classical.choose_spec h5
    have h7 : z' (e i) = z (Classical.choose h5) := by
      simp only [z']
      exact dif_pos h5
    rw [h7, h6]
  have h_w'_zero : ∀ j ∉ S, w' j = 0 := by
    intro j hj
    have h3 : ¬(∃ i : ι, e i = j) := by
      intro h4
      rcases h4 with ⟨i, h_eq⟩
      have h5 : j ∈ S := by
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ i, h_eq⟩
      exact hj h5
    have h4 : ∀ i : ι, e i ≠ j := by
      intro i
      intro h5
      exact h3 ⟨i, h5⟩
    simp only [w']
    have h_each_zero : ∀ i ∈ Finset.univ, (if e i = j then w i else 0) = 0 := by
      intro i _
      have h5 : e i ≠ j := h4 i
      simp [h5]
    rw [Finset.sum_eq_zero h_each_zero]
  have h_z'_in_s : ∀ j, z' j ∈ s := by
    intro j
    by_cases h : ∃ i : ι, e i = j
    · have hz' : z' j = z (Classical.choose h) := by
        simp only [z']; exact dif_pos h
      rw [hz']
      have h7 : z (Classical.choose h) ∈ Set.range z := ⟨Classical.choose h, rfl⟩
      exact hz_range h7
    · have hz' : z' j = x0 := by
        simp only [z']; exact dif_neg h
      rw [hz']; exact hx0
  have h_w'_nonneg : ∀ j, 0 ≤ w' j := by
    intro j
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> linarith [hw_nonneg i]
  have h_w'_sum : ∑ j : Fin N, w' j = 1 := by
    calc
      ∑ j : Fin N, w' j
        = ∑ j ∈ S, w' j := by
          rw [Finset.sum_subset S.subset_univ]
          intro j _ hj; exact h_w'_zero j hj
      _ = ∑ i : ι, w' (e i) := by
          rw [Finset.sum_image h_inj] <;> rfl
      _ = ∑ i : ι, w i := by
          apply Finset.sum_congr rfl; intro i _; exact h_w'_at_e i
      _ = 1 := hw_sum
  have h_eval : ∑ j : Fin N, w' j • z' j = ∑ i : ι, w i • z i := by
    calc
      ∑ j : Fin N, w' j • z' j
        = ∑ j ∈ S, w' j • z' j := by
          rw [Finset.sum_subset S.subset_univ]
          intro j _ hj
          have h2 : w' j = 0 := h_w'_zero j hj
          rw [h2] <;> simp
      _ = ∑ i : ι, w' (e i) • z' (e i) := by
          rw [Finset.sum_image h_inj] <;> rfl
      _ = ∑ i : ι, w i • z i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_w'_at_e i, h_z'_at_e i]
  exact ⟨w', z', ⟨h_w'_nonneg, h_w'_sum⟩, h_z'_in_s, h_eval⟩

/-- In any finite-dimensional real normed space, the convex hull of a compact set is compact.
Proof via Carathéodory's theorem: every point in the convex hull is a convex combination
of at most `finrank + 1` points, so the convex hull is a continuous image of a compact
parameter set (simplex × points). -/
theorem convexHull_compact_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  by_cases h_empty : s = ∅
  · rw [h_empty, convexHull_empty]
    exact isCompact_empty
  · rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨x0, hx0⟩
    let d := Module.finrank ℝ E
    let N := d + 1
    let paramSet : Set ((Fin N → ℝ) × (Fin N → E)) :=
      {p | p.1 ∈ stdSimplex ℝ (Fin N) ∧ ∀ i : Fin N, p.2 i ∈ s}
    have h_simplex_compact : IsCompact (stdSimplex ℝ (Fin N)) :=
      isCompact_stdSimplex ℝ (Fin N)
    have h_pi_compact : IsCompact {z : Fin N → E | ∀ i, z i ∈ s} := by
      have h : IsCompact (Set.pi Set.univ (fun (_ : Fin N) => s)) :=
        isCompact_univ_pi (fun _ => hs)
      simpa [Set.pi] using h
    have h_param_compact : IsCompact paramSet := by
      have h1 : paramSet = (stdSimplex ℝ (Fin N)) ×ˢ {z : Fin N → E | ∀ i, z i ∈ s} := by
        ext ⟨w, z⟩
        simp [paramSet] <;> rfl
      rw [h1]
      exact h_simplex_compact.prod h_pi_compact
    let eval : ((Fin N → ℝ) × (Fin N → E)) → E :=
      fun p => ∑ i : Fin N, p.1 i • p.2 i
    have h_eval_cont : Continuous eval := by fun_prop
    have h_main : convexHull ℝ s = eval '' paramSet := by
      apply Set.Subset.antisymm
      · -- convexHull ⊆ eval '' paramSet via Carathéodory
        intro x hx
        rcases eq_pos_convex_span_of_mem_convexHull hx with
          ⟨ι, _hfin, z, w, hz_range, h_aff, h_pos, h_sum, h_eq⟩
        have h_card1 : Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
          h_aff.card_le_finrank_succ
        have h_card2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
          Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        have h_card : Fintype.card ι ≤ N := by
          dsimp only [N]
          linarith
        have h_card' : Fintype.card ι ≤ Fintype.card (Fin N) := by
          simpa [Fintype.card_fin] using h_card
        rcases Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin N) h_card' with ⟨e⟩
        rcases extend_convex_combination x0 hx0 e z w hz_range (fun i => (h_pos i).le) h_sum
          with ⟨w', z', h_w'_simplex, h_z'_in_s, h_eval_eq⟩
        have h_param : (w', z') ∈ paramSet := ⟨h_w'_simplex, h_z'_in_s⟩
        have h_final : eval (w', z') = x := by
          simpa [eval] using h_eval_eq.trans h_eq
        exact ⟨(w', z'), h_param, h_final⟩
      · -- eval '' paramSet ⊆ convexHull
        rintro x ⟨p, hp, rfl⟩
        rcases hp with ⟨h_simplex, h_z_in_s⟩
        rcases h_simplex with ⟨h_nonneg, h_sum⟩
        exact mem_convexHull_of_exists_fintype p.1 p.2 h_nonneg h_sum h_z_in_s rfl
    rw [h_main]
    exact h_param_compact.image h_eval_cont

theorem convex_hull_contact_set_compact {n : ℕ} {K : Set (E n)}
    (hK_comp : IsCompact K) :
    IsCompact (convexHull ℝ (fjContactSet K)) :=
  convexHull_compact_of_compact (fjContactSet_compact hK_comp)

/-! ## Strict separation -/

/-- Strict separation of a point `p` from a nonempty compact convex set `C`. -/
theorem strict_separation_point_from_compact_convex {n : ℕ}
    {C : Set (FritzJohnSpace n)} (hC_conv : Convex ℝ C)
    (hC_comp : IsCompact C) (hC_nonempty : C.Nonempty)
    {p : FritzJohnSpace n} (hp : p ∉ C) :
    ∃ (f : (FritzJohnSpace n) →L[ℝ] ℝ), f ≠ 0 ∧
      ∀ c ∈ C, f c < f p := by
  have hC_closed : IsClosed C := hC_comp.isClosed
  rcases geometric_hahn_banach_closed_point hC_conv hC_closed hp with ⟨f, u, h1, h2⟩
  have h_f_ne_zero : f ≠ 0 := by
    intro hf
    rcases hC_nonempty with ⟨c, hc⟩
    have h3 : f c < u := h1 c hc
    have h4 : u < f p := h2
    rw [hf] at h3 h4
    simp at h3 h4 <;> linarith
  refine ⟨f, h_f_ne_zero, fun c hc => ?_⟩
  have h3 : f c < u := h1 c hc
  have h4 : u < f p := h2
  linarith

/-! ## Riesz-type decomposition -/

/-- Swap the two components of a pair. -/
private def swapPair {n : ℕ} (p : Fin n × Fin n) : Fin n × Fin n :=
  (p.2, p.1)

private lemma sum_swapPair {n : ℕ} (f : (Fin n × Fin n) → ℝ) :
    ∑ p : Fin n × Fin n, f (swapPair p) = ∑ p : Fin n × Fin n, f p := by
  let e : (Fin n × Fin n) ≃ (Fin n × Fin n) :=
    { toFun := swapPair
      invFun := swapPair
      left_inv := by intro x; ext <;> simp [swapPair]
      right_inv := by intro x; ext <;> simp [swapPair] }
  exact Fintype.sum_equiv e (f ∘ swapPair) f (fun x => rfl)

/-- Every continuous linear functional on `MatrixEntries n` is given by
`Y ↦ ∑ p, M p * Y p` for some `M`. -/
theorem matrixEntries_dual_by_sum {n : ℕ}
    (f2 : (MatrixEntries n) →L[ℝ] ℝ) :
    ∃ (M : MatrixEntries n), ∀ (Y : MatrixEntries n),
      f2 Y = ∑ p : Fin n × Fin n, M p * Y p := by
  let M : MatrixEntries n := fun p => f2 (Pi.single p 1)
  use M
  intro Y
  have h_expand : Y = ∑ p : Fin n × Fin n, Y p • Pi.single p 1 := by
    ext x
    simp [Pi.single_apply, Finset.sum_ite_eq']
    <;> tauto
  have h1 : f2 Y = f2 (∑ p : Fin n × Fin n, Y p • Pi.single p 1) := by
    exact congr_arg f2 h_expand
  rw [h1]
  have h_sum : f2 (∑ p : Fin n × Fin n, Y p • Pi.single p 1) =
      ∑ p : Fin n × Fin n, f2 (Y p • Pi.single p 1) :=
    map_sum f2 (fun x => Y x • Pi.single x 1) Finset.univ
  rw [h_sum]
  have h3 : ∑ p : Fin n × Fin n, f2 (Y p • Pi.single p 1) =
      ∑ p : Fin n × Fin n, Y p * f2 (Pi.single p 1) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [f2.map_smul] <;> ring
  rw [h3]
  apply Finset.sum_congr rfl
  intro p _
  simp [M] <;> ring

/-- Decomposition of a functional on `FritzJohnSpace n`:
`f(x, Y) = v·x + traceMul M Y`, with M symmetric, for symmetric Y. -/
theorem riesz_decomposition {n : ℕ}
    (f : (FritzJohnSpace n) →L[ℝ] ℝ) :
    ∃ (v : E n) (M : MatrixEntries n),
      (entriesToMatrix M).IsSymm ∧
      ∀ (x : E n) (Y : MatrixEntries n),
        (entriesToMatrix Y).IsSymm →
        f (x, Y) = inner ℝ v x + traceMul M Y := by
  let f1 : (E n) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inl ℝ (E n) (MatrixEntries n))
  let f2 : (MatrixEntries n) →L[ℝ] ℝ :=
    f.comp (ContinuousLinearMap.inr ℝ (E n) (MatrixEntries n))
  have h_add : ∀ (x : E n) (Y : MatrixEntries n),
      f (x, Y) = f1 x + f2 Y := by
    intro x Y
    have h : (x, Y) = (x, (0 : MatrixEntries n)) + ((0 : E n), Y) := by
      ext <;> simp
    rw [h, f.map_add] <;> rfl
  -- Riesz on E(n)
  have h1 : ∃ (v : E n), ∀ x, f1 x = inner ℝ v x := by
    let toDual : (E n) ≃ₗᵢ⋆[ℝ] (StrongDual ℝ (E n)) :=
      InnerProductSpace.toDual ℝ (E n)
    let v : E n := toDual.symm f1
    refine ⟨v, fun x => ?_⟩
    have h2 : toDual v = f1 := by simp [toDual, v]
    have h3 : (toDual v) x = inner ℝ v x := by rfl
    rw [h2] at h3
    exact h3
  rcases h1 with ⟨v, hv⟩
  -- Dual of matrix entries via sum
  rcases matrixEntries_dual_by_sum f2 with ⟨M0, hM0⟩
  -- Symmetrize M0: M(i,j) = (M0(i,j) + M0(j,i)) / 2
  let M : MatrixEntries n := fun p => (M0 p + M0 (swapPair p)) / 2
  have hM_symm : (entriesToMatrix M).IsSymm := by
    ext i j
    simp [entriesToMatrix, M, swapPair]
    <;> ring
  have hM_trace : ∀ (Y : MatrixEntries n), (entriesToMatrix Y).IsSymm →
      traceMul M Y = ∑ p : Fin n × Fin n, M0 p * Y p := by
    intro Y hY
    have hY_symm : ∀ (p : Fin n × Fin n), Y (swapPair p) = Y p := by
      intro p
      have h5 : (entriesToMatrix Y).transpose = (entriesToMatrix Y) := hY
      have h6 : (entriesToMatrix Y) p.2 p.1 = (entriesToMatrix Y) p.1 p.2 := by
        have h7 := congr_fun (congr_fun h5 p.2) p.1
        simpa [Matrix.transpose_apply] using Eq.symm h7
      simpa [entriesToMatrix, swapPair] using h6
    have h_trace_form : traceMul M Y = ∑ p : Fin n × Fin n, M p * Y (swapPair p) := by
      dsimp only [traceMul]
      have h : (∑ i : Fin n, ∑ j : Fin n, M (i, j) * Y (j, i)) =
               ∑ p : Fin n × Fin n, M (p.1, p.2) * Y (p.2, p.1) :=
        Eq.symm (Fintype.sum_prod_type fun x : Fin n × Fin n => M (x.1, x.2) * Y (x.2, x.1))
      simpa [swapPair] using h
    rw [h_trace_form]
    have h21 : ∀ (p : Fin n × Fin n),
        ((M0 p + M0 (swapPair p)) / 2) * Y (swapPair p) =
        (1 / 2 : ℝ) * (M0 p * Y (swapPair p)) +
        (1 / 2 : ℝ) * (M0 (swapPair p) * Y (swapPair p)) := by
      intro p; ring
    have h22 : ∑ p : Fin n × Fin n, M p * Y (swapPair p) =
        ∑ p : Fin n × Fin n, ((1 / 2 : ℝ) * (M0 p * Y (swapPair p)) +
          (1 / 2 : ℝ) * (M0 (swapPair p) * Y (swapPair p))) := by
      apply Finset.sum_congr rfl
      intro p _
      simpa [M] using h21 p
    rw [h22]
    have h_sum_add : ∑ p : Fin n × Fin n, ((1 / 2 : ℝ) * (M0 p * Y (swapPair p)) +
          (1 / 2 : ℝ) * (M0 (swapPair p) * Y (swapPair p))) =
        (∑ p : Fin n × Fin n, (1 / 2 : ℝ) * (M0 p * Y (swapPair p))) +
        ∑ p : Fin n × Fin n, (1 / 2 : ℝ) * (M0 (swapPair p) * Y (swapPair p)) := by
      rw [Finset.sum_add_distrib]
    rw [h_sum_add]
    have h_mul1 : ∑ p : Fin n × Fin n, (1 / 2 : ℝ) * (M0 p * Y (swapPair p)) =
        (1 / 2 : ℝ) * ∑ p : Fin n × Fin n, M0 p * Y (swapPair p) := by
      rw [Finset.mul_sum]
    have h_mul2 : ∑ p : Fin n × Fin n, (1 / 2 : ℝ) * (M0 (swapPair p) * Y (swapPair p)) =
        (1 / 2 : ℝ) * ∑ p : Fin n × Fin n, M0 (swapPair p) * Y (swapPair p) := by
      rw [Finset.mul_sum]
    rw [h_mul1, h_mul2]
    have h3 : ∑ p : Fin n × Fin n, M0 (swapPair p) * Y (swapPair p) =
                 ∑ p : Fin n × Fin n, M0 p * Y p := by
      exact sum_swapPair (fun q => M0 q * Y q)
    have h4 : ∑ p : Fin n × Fin n, M0 p * Y (swapPair p) =
                 ∑ p : Fin n × Fin n, M0 p * Y p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hY_symm p]
    rw [h4, h3] <;> ring
  refine ⟨v, M, hM_symm, fun x Y hY => ?_⟩
  rw [h_add x Y, hv x, hM0 Y, ← hM_trace Y hY]

/-! ## Generic separation (any real normed space) -/

/-- Generic strict separation: a point `p` from a nonempty compact convex set `C`
in any real normed space. -/
theorem strict_separation_generic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC_conv : Convex ℝ C) (hC_comp : IsCompact C)
    (hC_nonempty : C.Nonempty) {p : E} (hp : p ∉ C) :
    ∃ (f : E →L[ℝ] ℝ), f ≠ 0 ∧ ∀ c ∈ C, f c < f p := by
  have hC_closed : IsClosed C := hC_comp.isClosed
  rcases geometric_hahn_banach_closed_point hC_conv hC_closed hp with ⟨f, u, h1, h2⟩
  have h_f_ne_zero : f ≠ 0 := by
    intro hf
    rcases hC_nonempty with ⟨c, hc⟩
    have h3 : f c < u := h1 c hc
    have h4 : u < f p := h2
    rw [hf] at h3 h4
    simp at h3 h4 <;> linarith
  refine ⟨f, h_f_ne_zero, fun c hc => ?_⟩
  have h3 : f c < u := h1 c hc
  have h4 : u < f p := h2
  linarith

/-- Symmetric matrix dual representation: every continuous linear functional on
`Matrix (Fin n) (Fin n) ℝ` is given by Frobenius pairing with a symmetric matrix `M`,
when restricted to symmetric inputs. -/
theorem matrix_dual_symmetric {n : ℕ} (f : (Matrix (Fin n) (Fin n) ℝ) →L[ℝ] ℝ) :
    ∃ (M : Matrix (Fin n) (Fin n) ℝ), M.IsSymm ∧
      ∀ (N : Matrix (Fin n) (Fin n) ℝ), N.IsSymm →
        f N = ∑ i : Fin n, ∑ j : Fin n, M i j * N i j := by
  -- First get any matrix M0 representing f (copy of FritzJohn.matrix_dual_representation)
  let g : (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun N => ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j 1) * N i j
      map_add' := by
        intro N1 N2
        have h : ∀ (i j : Fin n), (N1 + N2) i j = N1 i j + N2 i j := by
          intro i j; rfl
        simp only [h, mul_add, Finset.sum_add_distrib]
        <;> rfl
      map_smul' := by
        intro c N
        have h1 : ∀ (i j : Fin n), (c • N) i j = c * N i j := by
          intro i j; rfl
        have h2 : ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j 1) * (c • N) i j =
                 ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j 1) * (c * N i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [h1 i j]
        rw [h2]
        have h3 : ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j 1) * (c * N i j) =
                 ∑ i : Fin n, ∑ j : Fin n, c * (f (Matrix.single i j 1) * N i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [h3]
        have h4 : ∑ i : Fin n, ∑ j : Fin n, c * (f (Matrix.single i j 1) * N i j) =
                 c * ∑ i : Fin n, ∑ j : Fin n, f (Matrix.single i j 1) * N i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        rw [h4] <;> rfl }
  let b : Module.Basis (Fin n × Fin n) ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    Matrix.stdBasis ℝ (Fin n) (Fin n)
  have h_unfold : ∀ (X : Matrix (Fin n) (Fin n) ℝ),
      g X = ∑ k : Fin n, ∑ l : Fin n, f (Matrix.single k l 1) * X k l := by
    intro X; rfl
  have h_basis : ∀ (p : Fin n × Fin n), f (b p) = g (b p) := by
    rintro ⟨i, j⟩
    have h_single : b (i, j) = Matrix.single i j (1 : ℝ) :=
      Matrix.stdBasis_eq_single ℝ (i := i) (j := j)
    have h1 : g (b (i, j)) = f (b (i, j)) := by
      rw [h_single]
      rw [h_unfold (Matrix.single i j 1)]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
        · simp [Matrix.single_apply]
        · intro k _ hkj
          have h : (Matrix.single i j (1 : ℝ)) i k = 0 := by
            rw [Matrix.single_apply (α := ℝ)]
            split_ifs <;> tauto
          exact mul_eq_zero.mpr (Or.inr h)
      · intro k _ hki
        have h : ∀ l : Fin n, (Matrix.single i j (1 : ℝ)) k l = 0 := by
          intro l
          rw [Matrix.single_apply (α := ℝ)]
          split_ifs <;> tauto
        have h_sum : ∑ l : Fin n, f (Matrix.single k l 1) * (Matrix.single i j (1 : ℝ)) k l = 0 := by
          apply Finset.sum_eq_zero
          intro l _
          have h' : (Matrix.single i j (1 : ℝ)) k l = 0 := h l
          exact mul_eq_zero.mpr (Or.inr h')
        exact h_sum
    exact h1.symm
  have h_eq : (f : (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] ℝ) = g := b.ext h_basis
  let M0 : Matrix (Fin n) (Fin n) ℝ := fun i j => f (Matrix.single i j 1)
  have h_rep : ∀ (N : Matrix (Fin n) (Fin n) ℝ),
      f N = ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j := by
    intro N
    have h5 : ((f : (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] ℝ) N) = g N := by
      rw [h_eq]
    have h6 : g N = ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j := by
      rfl
    exact Eq.trans h5 h6
  -- Symmetrize M0
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => (M0 i j + M0 j i) / 2
  have hM_symm : M.IsSymm := by
    ext i j
    simp [M, Matrix.transpose_apply] <;> ring
  have hM_trace : ∀ (N : Matrix (Fin n) (Fin n) ℝ), N.IsSymm →
      (∑ i : Fin n, ∑ j : Fin n, M i j * N i j) =
      ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j := by
    intro N hN
    have hN_symm : ∀ i j, N j i = N i j := by
      intro i j
      have h : N.transpose = N := hN
      have h_trans := congr_fun (congr_fun h j) i
      simpa [Matrix.transpose_apply] using Eq.symm h_trans
    have h_swap : ∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j =
                   ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j := by
      have h1 : ∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j =
                   ∑ i : Fin n, ∑ j : Fin n, M0 i j * N j i := by
        rw [Finset.sum_comm] <;> rfl
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hN_symm i j]
    have h_eq1 : ∑ i : Fin n, ∑ j : Fin n, M i j * N i j =
        ∑ i : Fin n, ∑ j : Fin n, ((M0 i j + M0 j i) / 2 * N i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rfl
    have h_eq2 : ∑ i : Fin n, ∑ j : Fin n, ((M0 i j + M0 j i) / 2 * N i j) =
        (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j) +
        (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j) := by
      have h_distrib : ∑ i : Fin n, ∑ j : Fin n, ((M0 i j + M0 j i) / 2 * N i j) =
          ∑ i : Fin n, ∑ j : Fin n, (M0 i j * N i j * (1 / 2 : ℝ) + M0 j i * N i j * (1 / 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h_distrib]
      have h_sum : ∑ i : Fin n, ∑ j : Fin n, (M0 i j * N i j * (1 / 2 : ℝ) + M0 j i * N i j * (1 / 2 : ℝ)) =
          (∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ)) +
          (∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ)) := by
        have h1 : ∀ i, ∑ j : Fin n, (M0 i j * N i j * (1 / 2 : ℝ) + M0 j i * N i j * (1 / 2 : ℝ)) =
            (∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ)) +
            (∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ)) := by
          intro i
          rw [Finset.sum_add_distrib]
        have h2 : ∑ i : Fin n, ∑ j : Fin n, (M0 i j * N i j * (1 / 2 : ℝ) + M0 j i * N i j * (1 / 2 : ℝ)) =
            ∑ i : Fin n, ((∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ)) + (∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h1 i
        rw [h2, Finset.sum_add_distrib]
      rw [h_sum]
      have h3 : ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ) =
                 (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j) := by
        have h31 : ∑ i : Fin n, ∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ) =
                   ∑ i : Fin n, (1 / 2 : ℝ) * ∑ j : Fin n, M0 i j * N i j := by
          apply Finset.sum_congr rfl
          intro i _
          have h : ∑ j : Fin n, M0 i j * N i j * (1 / 2 : ℝ) =
                     (∑ j : Fin n, M0 i j * N i j) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
          rw [h] <;> ring
        rw [h31, Finset.mul_sum] <;> rfl
      have h4 : ∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ) =
                 (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j) := by
        have h41 : ∑ i : Fin n, ∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ) =
                   ∑ i : Fin n, (1 / 2 : ℝ) * ∑ j : Fin n, M0 j i * N i j := by
          apply Finset.sum_congr rfl
          intro i _
          have h : ∑ j : Fin n, M0 j i * N i j * (1 / 2 : ℝ) =
                     (∑ j : Fin n, M0 j i * N i j) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
          rw [h]
          <;> ring
        rw [h41, Finset.mul_sum] <;> rfl
      rw [h3, h4] <;> ring
    rw [h_eq1, h_eq2, h_swap] <;> ring
  refine ⟨M, hM_symm, fun N hN => ?_⟩
  rw [h_rep N, ← hM_trace N hN]

end JohnEllipsoid
