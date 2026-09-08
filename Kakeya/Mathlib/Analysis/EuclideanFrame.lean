/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# General Euclidean / inner-product-space helpers

Dimension-free, project-type-free lemmas about Euclidean spaces and inner product
spaces: a sup-norm bound on the Euclidean norm, an inner-product width bound for a
set contained in the closed thickening of an affine subspace, and a Gram-Schmidt
style construction of an orthonormal frame orthogonal to a descending family of
subspaces.
-/

@[expose] public section

open scoped InnerProductSpace

/-- Bound on Euclidean norm of an element of `EuclideanSpace ℝ (Fin n)` in terms of
sup-norm of its coordinates. -/
lemma euclidean_norm_le (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hM : 0 ≤ M) (h : ∀ i, |x.ofLp i| ≤ M) : ‖x‖ ≤ Real.sqrt n * M := by
  rw [EuclideanSpace.norm_eq]
  have hsum_le : ∑ i, ‖x.ofLp i‖ ^ 2 ≤ (n : ℝ) * M ^ 2 := by
    calc ∑ i, ‖x.ofLp i‖ ^ 2
        ≤ ∑ _ : Fin n, M ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (n : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖x.ofLp i‖ ^ 2)
      ≤ Real.sqrt ((n : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsum_le
    _ = Real.sqrt n * M := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM]

/-- If a unit vector `e` is orthogonal to the *direction* of an affine subspace `A`,
and `K ⊆ cthickening(t, A)`, then for any `x, y ∈ K`, `|⟨e, x - y⟩| ≤ 2 t`.

Reasoning: the inner product `⟨e, ·⟩` is constant on `A`. Pick `a ∈ A` closest to
`x` (within `t`) and `a' ∈ A` closest to `y` (within `t`). Then
`⟨e, x - y⟩ = ⟨e, x - a⟩ + ⟨e, a' - y⟩` (since `⟨e, a - a'⟩ = 0`), and each term is
bounded by Cauchy-Schwarz by `t`. -/
lemma inner_diff_le_of_thickening
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (K : Set E) (A : AffineSubspace ℝ E)
    (hA_closed : IsClosed (A : Set E))
    (t : ℝ) (ht_nn : 0 ≤ t) (hK_thick : K ⊆ Metric.cthickening t A)
    (e : E) (he_norm : ‖e‖ = 1)
    (he_perp : e ∈ (A.direction : Submodule ℝ E)ᗮ)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    |inner ℝ e (x - y)| ≤ 2 * t := by
  have hxc := hK_thick hx
  rw [hA_closed.cthickening_eq_biUnion_closedBall ht_nn] at hxc
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hxc
  obtain ⟨a, ha, hxa⟩ := hxc
  have hyc := hK_thick hy
  rw [hA_closed.cthickening_eq_biUnion_closedBall ht_nn] at hyc
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hyc
  obtain ⟨a', ha', hya'⟩ := hyc
  have hsplit : x - y = (x - a) + (a - a') + (a' - y) := by abel
  have h_aa' : (a - a') ∈ A.direction :=
    AffineSubspace.vsub_mem_direction ha ha'
  have h_inner_zero : inner ℝ e (a - a') = (0 : ℝ) := by
    have := (Submodule.mem_orthogonal (A.direction) e).mp he_perp (a - a') h_aa'
    rwa [real_inner_comm] at this
  have hinner_eq : inner ℝ e (x - y) =
      inner ℝ e (x - a) + inner ℝ e (a' - y) := by
    rw [hsplit, inner_add_right, inner_add_right, h_inner_zero, add_zero]
  rw [hinner_eq]
  have h1 : |inner ℝ e (x - a)| ≤ ‖x - a‖ := by
    calc |inner ℝ e (x - a)|
        ≤ ‖e‖ * ‖x - a‖ := abs_real_inner_le_norm e (x - a)
      _ = ‖x - a‖ := by rw [he_norm, one_mul]
  have h2 : |inner ℝ e (a' - y)| ≤ ‖a' - y‖ := by
    calc |inner ℝ e (a' - y)|
        ≤ ‖e‖ * ‖a' - y‖ := abs_real_inner_le_norm e (a' - y)
      _ = ‖a' - y‖ := by rw [he_norm, one_mul]
  have hxa_norm : ‖x - a‖ ≤ t := by
    rw [← dist_eq_norm]; exact hxa
  have hay_norm : ‖a' - y‖ ≤ t := by
    rw [← dist_eq_norm, dist_comm]; exact hya'
  calc |inner ℝ e (x - a) + inner ℝ e (a' - y)|
      ≤ |inner ℝ e (x - a)| + |inner ℝ e (a' - y)| := abs_add_le _ _
    _ ≤ ‖x - a‖ + ‖a' - y‖ := add_le_add h1 h2
    _ ≤ t + t := add_le_add hxa_norm hay_norm
    _ = 2 * t := by ring

/-- Given a family of subspaces `W : Fin n → Submodule ℝ E` with
`finrank (W j) ≤ j.val` (where `n = finrank ℝ E`), construct an orthonormal frame
`e : Fin n → E` such that `e j ⊥ W ⟨n-1-j, _⟩` for every `j`. The construction is
Gram-Schmidt on the orthogonal complements `(W ⟨n-1-j, _⟩)ᗮ`, each of codimension
≤ `n-1-j`, hence of dimension ≥ `j+1`. -/
lemma onb_from_orth_family
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Fin (Module.finrank ℝ E) → Submodule ℝ E}
    (hW : ∀ j : Fin (Module.finrank ℝ E), Module.finrank ℝ (W j) ≤ j.val) :
    ∃ e : Fin (Module.finrank ℝ E) → E,
      Orthonormal ℝ e ∧
        ∀ j : Fin (Module.finrank ℝ E),
          e j ∈ (W ⟨Module.finrank ℝ E - 1 - j.val,
                    by rcases j with ⟨v, hv⟩; simp; omega⟩)ᗮ := by
  classical
  suffices h : ∀ k : ℕ, k ≤ Module.finrank ℝ E →
      ∃ e : Fin k → E, Orthonormal ℝ e ∧
      ∀ j : Fin k,
        ∀ (hj : Module.finrank ℝ E - 1 - j.val < Module.finrank ℝ E),
        e j ∈ (W ⟨Module.finrank ℝ E - 1 - j.val, hj⟩)ᗮ by
    obtain ⟨e, h_on, h_perp⟩ := h _ le_rfl
    refine ⟨e, h_on, fun j => ?_⟩
    apply h_perp
  intro k hk
  induction k with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · exact Orthonormal.of_isEmpty _
      · intro j; exact j.elim0
  | succ k ih =>
      obtain ⟨e, h_on, h_perp⟩ := ih (by omega)
      have hk_lt : k < Module.finrank ℝ E := hk
      have hk_lt' : Module.finrank ℝ E - 1 - k < Module.finrank ℝ E := by omega
      set Wperp : Submodule ℝ E :=
        (W ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩)ᗮ with hWperp_def
      set S : Submodule ℝ E := Submodule.span ℝ (Set.range e) with hS_def
      set Sperp : Submodule ℝ E := Sᗮ with hSperp_def
      have hW_le : Module.finrank ℝ (W ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩) ≤
          Module.finrank ℝ E - 1 - k := hW ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩
      have hWperp_ge : k + 1 ≤ Module.finrank ℝ Wperp := by
        have h_eq : Module.finrank ℝ (W ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩) +
            Module.finrank ℝ Wperp = Module.finrank ℝ E := by
          have := Submodule.finrank_add_finrank_orthogonal
            (𝕜 := ℝ) (E := E) (W ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩)
          simpa [hWperp_def] using this
        omega
      have hS_le : Module.finrank ℝ S ≤ k := by
        have h_lin : LinearIndependent ℝ e := h_on.linearIndependent
        have h_eq : Module.finrank ℝ S = k := by
          have := finrank_span_eq_card (R := ℝ) (M := E) h_lin
          simpa [hS_def, Fintype.card_fin] using this
        omega
      have hSperp_ge : Module.finrank ℝ E - k ≤ Module.finrank ℝ Sperp := by
        have h_eq : Module.finrank ℝ S + Module.finrank ℝ Sperp =
            Module.finrank ℝ E := by
          have := Submodule.finrank_add_finrank_orthogonal
            (𝕜 := ℝ) (E := E) S
          simpa [hSperp_def] using this
        omega
      have h_inter_pos : 1 ≤ Module.finrank ℝ
          ((Wperp ⊓ Sperp : Submodule ℝ E)) := by
        have h_sup_le : Module.finrank ℝ
            ((Wperp ⊔ Sperp : Submodule ℝ E)) ≤ Module.finrank ℝ E :=
          (Wperp ⊔ Sperp).finrank_le
        have h_eq : Module.finrank ℝ ((Wperp ⊔ Sperp : Submodule ℝ E)) +
            Module.finrank ℝ ((Wperp ⊓ Sperp : Submodule ℝ E)) =
            Module.finrank ℝ Wperp + Module.finrank ℝ Sperp :=
          Submodule.finrank_sup_add_finrank_inf_eq Wperp Sperp
        omega
      have h_inter_ne_bot : (Wperp ⊓ Sperp : Submodule ℝ E) ≠ ⊥ := by
        intro h_bot
        rw [h_bot] at h_inter_pos
        simp at h_inter_pos
      obtain ⟨v, hv_mem, hv_ne⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot h_inter_ne_bot
      have hv_W : v ∈ Wperp := (Submodule.mem_inf.mp hv_mem).1
      have hv_S : v ∈ Sperp := (Submodule.mem_inf.mp hv_mem).2
      have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
      let u : E := (‖v‖)⁻¹ • v
      have hu_norm : ‖u‖ = 1 := by
        change ‖(‖v‖)⁻¹ • v‖ = 1
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hv_norm_pos]
        field_simp
      have hu_W : u ∈ Wperp := Submodule.smul_mem _ _ hv_W
      have hu_S : u ∈ Sperp := Submodule.smul_mem _ _ hv_S
      have h_inner_u_e : ∀ i : Fin k, inner ℝ u (e i) = 0 := by
        intro i
        have h1 : e i ∈ S := Submodule.subset_span (Set.mem_range_self i)
        have h2 := (Submodule.mem_orthogonal _ _).mp hu_S (e i) h1
        rw [real_inner_comm]
        exact h2
      refine ⟨Fin.snoc e u, ?_, ?_⟩
      · rw [orthonormal_iff_ite]
        intro i j
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_last, if_true]
            rw [real_inner_self_eq_norm_sq, hu_norm]
            ring
          | cast j =>
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            rw [if_neg (Fin.castSucc_lt_last j).ne']
            exact h_inner_u_e j
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            rw [if_neg (Fin.castSucc_lt_last i).ne, real_inner_comm]
            exact h_inner_u_e i
          | cast j =>
            simp only [Fin.snoc_castSucc]
            have h_eq := (orthonormal_iff_ite (𝕜 := ℝ)).mp h_on i j
            by_cases hij : i = j
            · subst hij
              rw [if_pos rfl] at h_eq
              rw [if_pos rfl]
              exact h_eq
            · have hne_cast : i.castSucc ≠ j.castSucc := by
                intro h
                exact hij (Fin.castSucc_injective _ h)
              rw [if_neg hij] at h_eq
              rw [if_neg hne_cast]
              exact h_eq
      · intro j
        induction j using Fin.lastCases with
        | last =>
          intro hj
          rw [Fin.snoc_last]
          have hWeq : W ⟨Module.finrank ℝ E - 1 - (Fin.last k).val, hj⟩ =
                      W ⟨Module.finrank ℝ E - 1 - k, hk_lt'⟩ := by
            apply congrArg
            apply Fin.ext
            simp
          rw [hWeq]
          exact hu_W
        | cast j =>
          intro hj
          rw [Fin.snoc_castSucc]
          have h_idx : j.castSucc.val = j.val := Fin.val_castSucc j
          have hj' : Module.finrank ℝ E - 1 - j.val < Module.finrank ℝ E := by
            rw [← h_idx]; exact hj
          have hWeq : W ⟨Module.finrank ℝ E - 1 - j.castSucc.val, hj⟩ =
                      W ⟨Module.finrank ℝ E - 1 - j.val, hj'⟩ := by
            apply congrArg
            apply Fin.ext
            simp
          rw [hWeq]
          exact h_perp j hj'

section InnerProductUnit

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For unit vectors `d₁, d₂ : E` with `‖d₁ - d₂‖ ≤ ε`,
the inner product `⟨d₁, d₂⟩` is at least `1 - ε² / 2`. -/
lemma inner_unit_lower_bound_of_norm_sub_le
    {d₁ d₂ : E} (hd₁ : ‖d₁‖ = 1) (hd₂ : ‖d₂‖ = 1)
    {ε : ℝ} (hε : ‖d₁ - d₂‖ ≤ ε) :
    1 - ε ^ 2 / 2 ≤ inner ℝ d₁ d₂ := by
  have hnn : (0 : ℝ) ≤ ‖d₁ - d₂‖ := norm_nonneg _
  have hε_nn : (0 : ℝ) ≤ ε := hnn.trans hε
  have hsq_le : ‖d₁ - d₂‖ ^ 2 ≤ ε ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hε hε hnn hε_nn
  have hsq : ‖d₁ - d₂‖ ^ 2 = 2 - 2 * (inner ℝ d₁ d₂ : ℝ) := by
    rw [norm_sub_sq_real, hd₁, hd₂]; ring
  linarith

/-- Perpendicular-component frame-shift: if `u, u'` are two unit vectors and `w` is any vector,
the perpendicular projections of `w` onto the hyperplanes orthogonal to `u` and `u'` differ by
at most `2 ‖w‖ ‖u - u'‖`. -/
lemma perp_component_frame_shift (w u u' : E)
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    ‖(w - (inner ℝ w u') • u') - (w - (inner ℝ w u) • u)‖
      ≤ 2 * ‖w‖ * ‖u - u'‖ := by
  -- Simplify the LHS: (w - α'•u') - (w - α•u) = α•u - α'•u'
  have hsimp : (w - (inner ℝ w u') • u') - (w - (inner ℝ w u) • u)
      = (inner ℝ w u) • u - (inner ℝ w u') • u' := by
    abel
  rw [hsimp]
  -- Decompose: α•u - α'•u' = α•(u - u') + (α - α')•u'
  have hdec : (inner ℝ w u) • u - (inner ℝ w u') • u'
      = (inner ℝ w u) • (u - u') + ((inner ℝ w u) - (inner ℝ w u')) • u' := by
    rw [smul_sub, sub_smul]
    abel
  rw [hdec]
  -- Triangle inequality
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hu']
  -- Bound |⟨w,u⟩| ≤ ‖w‖
  have h1 : |inner ℝ w u| ≤ ‖w‖ := by
    have := abs_real_inner_le_norm w u
    rw [hu, mul_one] at this
    exact this
  -- Bound |⟨w,u⟩ - ⟨w,u'⟩| ≤ ‖w‖ * ‖u - u'‖
  have h2 : |inner ℝ w u - inner ℝ w u'| ≤ ‖w‖ * ‖u - u'‖ := by
    have heq : inner ℝ w u - inner ℝ w u' = inner ℝ w (u - u') := by
      rw [inner_sub_right]
    rw [heq]
    exact abs_real_inner_le_norm w (u - u')
  have hnonneg : 0 ≤ ‖u - u'‖ := norm_nonneg _
  have hwnn : 0 ≤ ‖w‖ := norm_nonneg _
  have hT1 : |inner ℝ w u| * ‖u - u'‖ ≤ ‖w‖ * ‖u - u'‖ :=
    mul_le_mul_of_nonneg_right h1 hnonneg
  have hT2 : |inner ℝ w u - inner ℝ w u'| * 1 ≤ ‖w‖ * ‖u - u'‖ * 1 :=
    mul_le_mul_of_nonneg_right h2 zero_le_one
  linarith

/-- Parallel-component frame-shift: if `u, u'` are two unit vectors and `w` is any vector,
the parallel components `⟪w, u⟫` and `⟪w, u'⟫` differ by at most `‖w‖ ‖u - u'‖`. -/
lemma par_component_frame_shift (w u u' : E)
    (_hu : ‖u‖ = 1) (_hu' : ‖u'‖ = 1) :
    |inner ℝ w u' - inner ℝ w u| ≤ ‖w‖ * ‖u - u'‖ := by
  have heq : inner ℝ w u' - inner ℝ w u = inner ℝ w (u' - u) := by
    rw [inner_sub_right]
  rw [heq]
  have hbd : |inner ℝ w (u' - u)| ≤ ‖w‖ * ‖u' - u‖ :=
    abs_real_inner_le_norm w (u' - u)
  rwa [norm_sub_rev] at hbd

/-- The component of `v` orthogonal to a unit vector `u` has norm at most `2 * ‖v‖`. -/
lemma norm_perp_le_two_mul_norm {u : E} (hu : ‖u‖ = 1) (v : E) :
    ‖v - (inner ℝ v u) • u‖ ≤ 2 * ‖v‖ := by
  calc
    ‖v - (inner ℝ v u) • u‖ ≤ ‖v‖ + ‖(inner ℝ v u) • u‖ := norm_sub_le _ _
    _ = ‖v‖ + (‖inner ℝ v u‖ * ‖u‖) := by rw [norm_smul]
    _ = ‖v‖ + (|inner ℝ v u| * ‖u‖) := by rw [Real.norm_eq_abs]
    _ = ‖v‖ + |inner ℝ v u| := by rw [hu, mul_one]
    _ ≤ ‖v‖ + (‖v‖ * ‖u‖) := by
      gcongr
      exact abs_real_inner_le_norm v u
    _ = ‖v‖ + ‖v‖ := by rw [hu, mul_one]
    _ = 2 * ‖v‖ := by ring

/-- If `m = t • d + c • u + z` with `u` a unit vector, `|t| ≤ 1 / 2`, `‖d - u‖ ≤ r` and
`‖z‖ ≤ ρ`, then the component of `m` orthogonal to `u` has norm at most `r + 2 * ρ`: the
`c • u` term is annihilated, `t • d` contributes `|t| * 2 * r` and `z` contributes
`2 * ρ`. -/
lemma norm_perp_le_of_decomp {u : E} (hu : ‖u‖ = 1) {m d z : E} {t c r ρ : ℝ}
    (hm : m = t • d + c • u + z) (ht : |t| ≤ 1 / 2)
    (hd : ‖d - u‖ ≤ r) (hz : ‖z‖ ≤ ρ) :
    ‖m - (inner ℝ m u) • u‖ ≤ r + 2 * ρ := by
  have hinner_uu : inner ℝ u u = 1 := by
    calc
      inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq _
      _ = 1 ^ 2 := by rw [hu]
      _ = 1 := by norm_num
  have hinner_du_minus_one : inner ℝ (d - u) u = inner ℝ d u - 1 := by
    calc
      inner ℝ (d - u) u = inner ℝ d u - inner ℝ u u := by rw [inner_sub_left]
      _ = inner ℝ d u - 1 := by rw [hinner_uu]
  have h_eq : d - (inner ℝ d u) • u = (d - u) - (inner ℝ (d - u) u) • u := by
    calc
      d - (inner ℝ d u) • u = (d - u) - ((inner ℝ d u) • u - u) := by
        abel
      _ = (d - u) - ((inner ℝ d u - 1) • u) := by simp [sub_smul, one_smul]
      _ = (d - u) - (inner ℝ (d - u) u) • u := by rw [hinner_du_minus_one]
  have hinner_mu : inner ℝ m u = t * inner ℝ d u + c + inner ℝ z u := by
    calc
      inner ℝ m u = inner ℝ (t • d + c • u + z) u := by rw [hm]
      _ = inner ℝ (t • d) u + inner ℝ (c • u) u + inner ℝ z u := by simp [inner_add_left]
      _ = t * inner ℝ d u + c * inner ℝ u u + inner ℝ z u := by simp [inner_smul_left]
      _ = t * inner ℝ d u + c * 1 + inner ℝ z u := by rw [hinner_uu]
      _ = t * inner ℝ d u + c + inner ℝ z u := by ring
  have key : m - (inner ℝ m u) • u =
      t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u) := by
    calc
      m - (inner ℝ m u) • u = (t • d + c • u + z) - (inner ℝ m u) • u := by rw [hm]
      _ = (t • d + c • u + z) - ((t * inner ℝ d u + c + inner ℝ z u) • u) := by rw [hinner_mu]
      _ = (t • d + c • u + z) - ((t * inner ℝ d u) • u + c • u + (inner ℝ z u) • u) := by
        simp [add_smul]
      _ = t • d - (t * inner ℝ d u) • u + z - (inner ℝ z u) • u := by
        abel
      _ = t • (d - (inner ℝ d u) • u) + (z - (inner ℝ z u) • u) := by
        simp [smul_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u) := by rw [h_eq]
  rw [key]
  have hnormA : ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ ≤ r := by
    calc
      ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ = |t| * ‖(d - u) - (inner ℝ (d - u) u) • u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * (2 * ‖d - u‖) := by
        refine mul_le_mul_of_nonneg_left (norm_perp_le_two_mul_norm hu (d - u)) (abs_nonneg _)
      _ = (|t| * 2) * ‖d - u‖ := by ring
      _ ≤ (1 : ℝ) * ‖d - u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc
          |t| * 2 = 2 * |t| := by ring
          _ ≤ 2 * (1 / 2) := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
          _ = 1 := by ring
      _ = ‖d - u‖ := by simp
      _ ≤ r := hd
  have hnormB : ‖z - (inner ℝ z u) • u‖ ≤ 2 * ρ := by
    calc
      ‖z - (inner ℝ z u) • u‖ ≤ 2 * ‖z‖ := norm_perp_le_two_mul_norm hu z
      _ ≤ 2 * ρ := mul_le_mul_of_nonneg_left hz (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖t • ((d - u) - (inner ℝ (d - u) u) • u) + (z - (inner ℝ z u) • u)‖
        ≤ ‖t • ((d - u) - (inner ℝ (d - u) u) • u)‖ + ‖z - (inner ℝ z u) • u‖ := norm_add_le _ _
    _ ≤ r + 2 * ρ := add_le_add hnormA hnormB

end InnerProductUnit

section DirectionBasis

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- Given a unit vector `d : E` in a finite-dimensional inner product space,
there exists an orthonormal basis of `E` (indexed by `Fin (Module.finrank ℝ E)`)
whose zeroth element equals `d`. -/
lemma exists_orthonormalBasis_zero_eq {d : E} (hd : ‖d‖ = 1) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, b 0 = d := by
  have h_orth : Orthonormal ℝ
      (({0} : Set (Fin (Module.finrank ℝ E))).restrict (fun _ => d)) := by
    refine ⟨?_, ?_⟩
    · intro _; simpa using hd
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (ι := Fin (Module.finrank ℝ E))
      (s := ({0} : Set (Fin (Module.finrank ℝ E))))
      (v := fun _ => d)
      (Fintype.card_fin _).symm h_orth
  exact ⟨b, hb 0 (Set.mem_singleton 0)⟩

/-- An orthonormal basis of `E` whose zeroth vector is a given unit vector `d`. -/
noncomputable def directionBasis {d : E} (hd : ‖d‖ = 1) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  (exists_orthonormalBasis_zero_eq hd).choose

@[simp]
lemma directionBasis_zero {d : E} (hd : ‖d‖ = 1) :
    directionBasis hd 0 = d :=
  (exists_orthonormalBasis_zero_eq hd).choose_spec

/-- The orthonormal-basis isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin (finrank ℝ E))`
arising from `directionBasis hd`. Maps the chosen unit direction `d` to the
zeroth standard basis vector. -/
noncomputable def cylinderEquiv {d : E} (hd : ‖d‖ = 1) :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (directionBasis hd).repr

@[simp]
lemma cylinderEquiv_apply_direction {d : E} (hd : ‖d‖ = 1) :
    cylinderEquiv hd d = EuclideanSpace.single 0 1 := by
  have h := (directionBasis hd).repr_self 0
  rw [directionBasis_zero hd] at h
  exact h

@[simp]
lemma cylinderEquiv_symm_single_zero {d : E} (hd : ‖d‖ = 1) :
    (cylinderEquiv hd).symm (EuclideanSpace.single 0 1) = d := by
  rw [← cylinderEquiv_apply_direction hd, LinearIsometryEquiv.symm_apply_apply]

end DirectionBasis

section Fin3Frame

/-- Expansion of an inner product over an orthonormal frame of `EuclideanSpace ℝ (Fin 3)`. -/
theorem inner_eq_sum_frame
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ u w : ℝ) = ∑ j : Fin 3, inner ℝ (basis j) w * inner ℝ u (basis j) :=
  (basis.sum_inner_mul_inner u w).symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

/-- Term-by-term bound for the frame expansion of `inner_eq_sum_frame`: the size of an inner
product is at most the sum over the frame of `|frame coordinate| * |cross-frame coefficient|`. -/
theorem abs_inner_le_sum_frame
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ u w : ℝ)| ≤ |inner ℝ (basis 0) w| * |inner ℝ u (basis 0)|
      + |inner ℝ (basis 1) w| * |inner ℝ u (basis 1)|
      + |inner ℝ (basis 2) w| * |inner ℝ u (basis 2)| := by
  rw [inner_eq_sum_frame basis u w, Fin.sum_univ_three, ← abs_mul, ← abs_mul, ← abs_mul]
  exact abs_add_three _ _ _

/-- Frame expansion with per-term bounds: a bound `dⱼ` on each frame coordinate of `w` together
with a bound `cⱼ` on each cross-frame coefficient of `u` bounds `⟪u, w⟫` by `∑ dⱼ cⱼ`. -/
theorem abs_inner_le_of_frame_bounds
    (basis : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (u w : EuclideanSpace ℝ (Fin 3)) {d₀ d₁ d₂ c₀ c₁ c₂ : ℝ}
    (h₀ : |(inner ℝ (basis 0) w : ℝ)| ≤ d₀) (h₁ : |(inner ℝ (basis 1) w : ℝ)| ≤ d₁)
    (h₂ : |(inner ℝ (basis 2) w : ℝ)| ≤ d₂)
    (k₀ : |(inner ℝ u (basis 0) : ℝ)| ≤ c₀) (k₁ : |(inner ℝ u (basis 1) : ℝ)| ≤ c₁)
    (k₂ : |(inner ℝ u (basis 2) : ℝ)| ≤ c₂) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    |(inner ℝ u w : ℝ)| ≤ d₀ * c₀ + d₁ * c₁ + d₂ * c₂ :=
  (abs_inner_le_sum_frame basis u w).trans <|
    add_le_add (add_le_add (mul_le_mul h₀ k₀ (abs_nonneg _) hd₀)
      (mul_le_mul h₁ k₁ (abs_nonneg _) hd₁)) (mul_le_mul h₂ k₂ (abs_nonneg _) hd₂)

/-- Cauchy–Schwarz between two orthonormal frames: every cross-frame coefficient is at most `1`
in absolute value. -/
theorem abs_inner_basis_le_one
    (basis basis' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (i j : Fin 3) :
    |(inner ℝ (basis i) (basis' j) : ℝ)| ≤ 1 :=
  (abs_real_inner_le_norm _ _).trans_eq (by rw [basis.norm_eq_one, basis'.norm_eq_one, mul_one])

/-- Triangle-inequality split of a coordinate of `x -ᵥ c` through an auxiliary point `p` and an
auxiliary centre `c'`. -/
theorem abs_inner_vsub_le_split (u x p c c' : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ u (x -ᵥ c) : ℝ)|
      ≤ |inner ℝ u (x -ᵥ c')| + |inner ℝ u (p -ᵥ c')| + |inner ℝ u (p -ᵥ c)| := by
  rw [show x -ᵥ c = (x -ᵥ c') - (p -ᵥ c') + (p -ᵥ c) by
        rw [vsub_sub_vsub_cancel_right, vsub_add_vsub_cancel],
    inner_add_right, inner_sub_right]
  exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)

end Fin3Frame
