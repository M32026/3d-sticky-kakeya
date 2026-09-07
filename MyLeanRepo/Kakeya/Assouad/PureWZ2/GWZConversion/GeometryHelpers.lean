import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.AssertionD

/-!
# Geometry helpers for the GWZ→WZ2 conversion

Reusable geometric lemmas independent of any particular cover strategy:

- `orthonormal_basis3`: extend a unit vector to a full orthonormal triple of `Point3`.
- `dilated_carrier_bounding_cylinder`: decompose a point in the A-dilated carrier
  into longitudinal + radial coordinates relative to the tube direction.
- `pythagorean_2d`: norm of a linear combination of two orthonormal vectors.
- `orthonormal_triple_facts`: extract inner-product/norm facts from an orthonormal triple.
- `abs_bound_implies`: turn an absolute-value bound into two-sided inequalities.
- `exists_nat_floor`, `exists_nat_round`: discrete rounding helpers for grid indexing.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductSpace

attribute [local instance] Classical.propDecidable

/--
Given a unit vector `v` in `Point3`, there exists an orthonormal basis
`(v, e1, e2)` of `Point3`.
-/
lemma orthonormal_basis3 (v : Point3) (hv : ‖v‖ = 1) :
    ∃ (e1 e2 : Point3),
      Orthonormal ℝ (![v, e1, e2] : Fin 3 → Point3) := by
  have hv_ne_zero : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  letI : Fact (Module.finrank ℝ Point3 = 3) := ⟨by simp [Point3]⟩
  let b : OrthonormalBasis (Fin 2) ℝ (ℝ ∙ v)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 2 hv_ne_zero
  let e1 : Point3 := (b 0).val
  let e2 : Point3 := (b 1).val
  have h1 : ‖e1‖ = 1 := by
    have h_b1 : ‖b 0‖ = 1 := b.orthonormal.1 0
    have h_eq : ‖(b 0 : Point3)‖ = ‖b 0‖ := by rfl
    rw [h_eq] at * <;> simpa [e1] using h_b1
  have h2 : ‖e2‖ = 1 := by
    have h_b2 : ‖b 1‖ = 1 := b.orthonormal.1 1
    have h_eq : ‖(b 1 : Point3)‖ = ‖b 1‖ := by rfl
    rw [h_eq] at * <;> simpa [e2] using h_b2
  have h12 : inner ℝ e1 e2 = 0 := by
    exact b.inner_eq_zero (by simp)
  have he1_perp : inner ℝ v e1 = 0 := by
    exact (b 0).property v (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
  have he2_perp : inner ℝ v e2 = 0 := by
    exact (b 1).property v (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
  have h_comm : ∀ (x y : Point3), inner ℝ x y = inner ℝ y x := by
    intro x y
    exact real_inner_comm y x
  have h_orth : Orthonormal ℝ (![v, e1, e2] : Fin 3 → Point3) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hv, h1, h2, he1_perp, he2_perp, h12, h_comm] <;> ring
  exact ⟨e1, e2, h_orth⟩

/--
Points in the A-dilated carrier lie in a bounding cylinder.

Given an orthonormal basis `(v, e1, e2)`, any point `x` in the A-dilated carrier
can be written as `x = m + t • v + a • e1 + b • e2` with
`|t| ≤ A/2 + A*ρ` and `a² + b² ≤ (A*ρ)²`.
-/
lemma dilated_carrier_bounding_cylinder
    {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 < A)
    (T : Kakeya.DeltaTube ρ)
    (e1 e2 : Point3)
    (h_orth : Orthonormal ℝ (![T.direction, e1, e2] : Fin 3 → Point3))
    (x : Point3)
    (hx : x ∈ wz2PaperCenteredDilatedCarrier A T) :
    ∃ (t a b : ℝ),
      x = wz2PaperTubeMidpoint T + t • T.direction + a • e1 + b • e2 ∧
      |t| ≤ A / 2 + A * ρ ∧
      a ^ 2 + b ^ 2 ≤ (A * ρ) ^ 2 := by
  let m : Point3 := wz2PaperTubeMidpoint T
  let v : Point3 := T.direction
  have hv : ‖v‖ = 1 := T.direction_unit
  have hA_nonneg : 0 ≤ A := by linarith
  let b3 : Fin 3 → Point3 := ![v, e1, e2]
  have h_basis_orth : Orthonormal ℝ b3 := h_orth
  have h_lin_indep : LinearIndependent ℝ b3 := h_basis_orth.linearIndependent
  have h_span : Submodule.span ℝ (Set.range b3) = ⊤ := by
    have h3 : Module.finrank ℝ Point3 = 3 := by simp [Point3]
    rw [h3] at *
    exact h_lin_indep.span_eq_top_of_card_eq_finrank (by simp)
  let b3' : OrthonormalBasis (Fin 3) ℝ Point3 :=
    OrthonormalBasis.mkOfOrthogonalEqBot h_basis_orth (by rw [h_span] <;> simp)
  have h_b3'_eq : ∀ (i : Fin 3), (b3' i : Point3) = b3 i := by
    have h : (b3' : Fin 3 → Point3) = b3 := OrthonormalBasis.coe_of_orthogonal_eq_bot_mk h_basis_orth _
    intro i; rw [h]
  rcases hx with ⟨z, hz, rfl⟩
  have h_seg_compact : IsCompact (unitSegment T.base v) := by
    have h : IsCompact ((fun t : ℝ => T.base + t • v) '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.image (by fun_prop)
    simpa [unitSegment] using h
  have h_exists : ∃ (y : Point3), y ∈ unitSegment T.base v ∧ dist z y ≤ ρ := by
    have h_eq : T.carrier = Metric.cthickening ρ (unitSegment T.base v) := by rfl
    rw [h_eq] at hz
    rw [h_seg_compact.cthickening_eq_biUnion_closedBall (by linarith)] at hz
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hz
  rcases h_exists with ⟨y, hy_seg, hdist_z⟩
  rcases hy_seg with ⟨s, hs, rfl⟩
  have hs_nonneg : 0 ≤ s := hs.1
  have hs_le_one : s ≤ 1 := hs.2
  let y_pt : Point3 := T.base + s • v
  let y' : Point3 := AffineMap.homothety m A y_pt
  have hdist : dist (AffineMap.homothety m A z) y' ≤ A * ρ := by
    have h_smul_sub : (AffineMap.homothety m A z) - y' = A • (z - y_pt) := by
      simp [y', AffineMap.homothety_apply, smul_sub] <;> abel
    have h1 : dist (AffineMap.homothety m A z) y' = ‖(AffineMap.homothety m A z) - y'‖ := by
      rw [dist_eq_norm]
    have h_norm_A : ‖A‖ = A := by
      simp [Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
    rw [h1, h_smul_sub, norm_smul, h_norm_A]
    exact mul_le_mul_of_nonneg_left hdist_z hA_nonneg
  let s0 : ℝ := A * (s - 1 / 2)
  have hy_eq : y' = m + s0 • v := by
    have h_m_eq : m = T.base + (1 / 2 : ℝ) • v := by
      simp [m, wz2PaperTubeMidpoint] <;> rfl
    have h : y' = m + A • (y_pt - m) := by
      simp [y', AffineMap.homothety_apply] <;> abel
    rw [h, h_m_eq]
    have h2 : y_pt - (T.base + (1 / 2 : ℝ) • v) = (s - 1 / 2 : ℝ) • v := by
      simp [y_pt, sub_smul, add_smul] <;> abel
    rw [h2]
    have h3 : A • ((s - 1 / 2 : ℝ) • v) = s0 • v := by
      rw [smul_smul] <;> rfl
    rw [h3] <;> rfl
  rw [hy_eq] at hdist
  let d : Point3 := (AffineMap.homothety m A z) - (m + s0 • v)
  have hdnorm : ‖d‖ ≤ A * ρ := by simpa [d, dist_eq_norm] using hdist
  let t_par : ℝ := inner ℝ d v
  let a : ℝ := inner ℝ d e1
  let b : ℝ := inner ℝ d e2
  have h_b3_0 : b3 0 = v := by simp [b3]
  have h_b3_1 : b3 1 = e1 := by simp [b3]
  have h_b3_2 : b3 2 = e2 := by simp [b3]
  have h_decomp : d = t_par • v + a • e1 + b • e2 := by
    have h_sum : (∑ i : Fin 3, inner ℝ (b3' i) d • b3' i) = d := b3'.sum_repr' d
    have h_comm : ∀ (i : Fin 3), inner ℝ (b3' i) d = inner ℝ d (b3' i) := by
      intro i
      exact real_inner_comm d (b3' i)
    have h_sum2 : (∑ i : Fin 3, inner ℝ d (b3' i) • b3' i) = d := by
      have h : (∑ i : Fin 3, inner ℝ (b3' i) d • b3' i) = ∑ i : Fin 3, inner ℝ d (b3' i) • b3' i := by
        apply Finset.sum_congr rfl; intro i _; rw [h_comm i]
      rw [←h]; exact h_sum
    have h_sum3 : (∑ i : Fin 3, inner ℝ d (b3' i) • b3' i) =
        inner ℝ d v • v + inner ℝ d e1 • e1 + inner ℝ d e2 • e2 := by
      have h_eval : (∑ i : Fin 3, inner ℝ d (b3' i) • b3' i) =
          inner ℝ d (b3' 0) • b3' 0 + inner ℝ d (b3' 1) • b3' 1 + inner ℝ d (b3' 2) • b3' 2 := by
        simp [Fin.sum_univ_succ] <;> abel
      rw [h_eval]
      have h0 : inner ℝ d (b3' 0) • b3' 0 = inner ℝ d v • v := by
        rw [h_b3'_eq 0, h_b3_0]
      have h1 : inner ℝ d (b3' 1) • b3' 1 = inner ℝ d e1 • e1 := by
        rw [h_b3'_eq 1, h_b3_1]
      have h2 : inner ℝ d (b3' 2) • b3' 2 = inner ℝ d e2 • e2 := by
        rw [h_b3'_eq 2, h_b3_2]
      rw [h0, h1, h2] <;> abel
    rw [h_sum3] at h_sum2
    simpa [t_par, a, b] using h_sum2.symm
  have h_norm_sq : ‖d‖ ^ 2 = t_par ^ 2 + a ^ 2 + b ^ 2 := by
    have h : (∑ i : Fin 3, (inner ℝ d (b3' i)) ^ 2) = ‖d‖ ^ 2 := b3'.sum_sq_inner_left d
    have h_comm : ∀ (i : Fin 3), inner ℝ (b3' i) d = inner ℝ d (b3' i) := by
      intro i
      exact real_inner_comm d (b3' i)
    have h2_sum : (∑ i : Fin 3, (inner ℝ d (b3' i)) ^ 2) =
        (inner ℝ d v) ^ 2 + (inner ℝ d e1) ^ 2 + (inner ℝ d e2) ^ 2 := by
      have h_eval : (∑ i : Fin 3, (inner ℝ d (b3' i)) ^ 2) =
          (inner ℝ d (b3' 0)) ^ 2 + (inner ℝ d (b3' 1)) ^ 2 + (inner ℝ d (b3' 2)) ^ 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_eval]
      have h0 : (inner ℝ d (b3' 0)) ^ 2 = (inner ℝ d v) ^ 2 := by
        rw [h_b3'_eq 0, h_b3_0]
      have h1 : (inner ℝ d (b3' 1)) ^ 2 = (inner ℝ d e1) ^ 2 := by
        rw [h_b3'_eq 1, h_b3_1]
      have h2' : (inner ℝ d (b3' 2)) ^ 2 = (inner ℝ d e2) ^ 2 := by
        rw [h_b3'_eq 2, h_b3_2]
      rw [h0, h1, h2'] <;> ring
    rw [h2_sum] at h
    simpa [t_par, a, b] using h.symm
  have hs0_lower : -A / 2 ≤ s0 := by
    dsimp only [s0]; nlinarith
  have hs0_upper : s0 ≤ A / 2 := by
    dsimp only [s0]; nlinarith
  have h_tpar_bound : |t_par| ≤ A * ρ := by
    have h : |t_par| ≤ ‖d‖ := by
      have h2 : |inner ℝ d v| ≤ ‖d‖ * ‖v‖ := abs_real_inner_le_norm d v
      rw [hv] at h2; simpa using h2
    calc |t_par| ≤ ‖d‖ := h
         _ ≤ A * ρ := hdnorm
  let t : ℝ := s0 + t_par
  have h_t_abs : |t| ≤ A / 2 + A * ρ := by
    have h_triangle : |s0 + t_par| ≤ |s0| + |t_par| :=
      abs_add_le s0 t_par
    have h_s0_abs : |s0| ≤ A / 2 := by
      rw [abs_le] <;> constructor <;> linarith
    calc |t| = |s0 + t_par| := by rfl
      _ ≤ |s0| + |t_par| := h_triangle
      _ ≤ A / 2 + A * ρ := by linarith [h_tpar_bound, h_s0_abs]
  have h_ab_bound : a ^ 2 + b ^ 2 ≤ (A * ρ) ^ 2 := by
    have h4 : a ^ 2 + b ^ 2 ≤ ‖d‖ ^ 2 := by
      have h_nonneg : 0 ≤ t_par ^ 2 := by positivity
      linarith [h_norm_sq]
    have h5 : ‖d‖ ^ 2 ≤ (A * ρ) ^ 2 := by
      have h6 : ‖d‖ ≤ A * ρ := hdnorm
      nlinarith [norm_nonneg d]
    linarith
  have h_x_eq : (AffineMap.homothety m A z) = m + t • v + a • e1 + b • e2 := by
    have h1 : (AffineMap.homothety m A z) = m + s0 • v + d := by
      simp [d] <;> abel
    rw [h1, h_decomp]
    simp [t, add_smul, sub_smul] <;> abel
  exact ⟨t, a, b, h_x_eq, h_t_abs, h_ab_bound⟩

/-- From `|a| ≤ b`, extract `-b ≤ a ∧ a ≤ b`. -/
lemma abs_bound_implies (a b : ℝ) (h : |a| ≤ b) : -b ≤ a ∧ a ≤ b := by
  by_cases h2 : 0 ≤ a
  · have h3 : |a| = a := abs_of_nonneg h2
    rw [h3] at h
    constructor <;> linarith
  · have h4 : a < 0 := by linarith
    have h5 : |a| = -a := abs_of_neg h4
    rw [h5] at h
    constructor <;> linarith

/--
Given `x ∈ [0, L]`, there exists `k : ℕ` with `k ≤ x < k+1` and `k ≤ Nat.ceil L`.
-/
lemma exists_nat_floor (x L : ℝ) (hx : 0 ≤ x) (hL : x ≤ L) :
    ∃ (k : ℕ), (k : ℝ) ≤ x ∧ x < (k : ℝ) + 1 ∧ k ≤ Nat.ceil L := by
  let n : Int := Int.floor x
  have h1 : (n : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : 0 ≤ n := by
    have h4 : (0 : Int) ≤ Int.floor x := by
      simpa [Int.le_floor] using hx
    exact h4
  let k : ℕ := n.toNat
  have hk : (k : ℝ) = (n : ℝ) := by
    have h5 : (k : Int) = n := Int.toNat_of_nonneg h3
    exact_mod_cast h5
  have hk1 : (k : ℝ) ≤ x := by rw [hk] <;> exact h1
  have hk2 : x < (k : ℝ) + 1 := by rw [hk] <;> exact h2
  have hk3 : k ≤ Nat.ceil L := by
    have h : (k : ℝ) ≤ L := by rw [hk] <;> linarith
    have h' : (k : ℝ) ≤ (Nat.ceil L : ℝ) := by linarith [Nat.le_ceil L]
    exact_mod_cast h'
  exact ⟨k, hk1, hk2, hk3⟩

/--
Given `y ∈ [0, R]` and `ρ₀ > 0`, there exists `i : ℕ` with
`|y - i * ρ₀| ≤ ρ₀ / 2` and `i ≤ Nat.ceil (R / ρ₀)`.
-/
lemma exists_nat_round (y R ρ₀ : ℝ) (hy : 0 ≤ y) (hR : y ≤ R) (hρ₀ : 0 < ρ₀) :
    ∃ (i : ℕ), |y - (i : ℝ) * ρ₀| ≤ ρ₀ / 2 ∧ i ≤ Nat.ceil (R / ρ₀) := by
  set z : ℝ := y / ρ₀ + 1 / 2 with hz_def
  have hz_nonneg : 0 ≤ z := by positivity
  have hz_le : z ≤ R / ρ₀ + 1 / 2 := by
    rw [hz_def]; have h : y ≤ R := hR; gcongr
  rcases exists_nat_floor z (R / ρ₀ + 1 / 2) hz_nonneg hz_le with ⟨i, hi1, hi2, _⟩
  have h4 : (i : ℝ) - 1 / 2 ≤ y / ρ₀ := by
    have h : (i : ℝ) ≤ z := hi1
    rw [hz_def] at h
    linarith
  have h5 : y / ρ₀ < (i : ℝ) + 1 / 2 := by
    have h : z < (i : ℝ) + 1 := hi2
    rw [hz_def] at h
    linarith
  have h6 : |y / ρ₀ - (i : ℝ)| ≤ 1 / 2 := by
    rw [abs_le] <;> constructor <;> linarith
  have h7 : |y - (i : ℝ) * ρ₀| ≤ ρ₀ / 2 := by
    have h8 : y - (i : ℝ) * ρ₀ = ρ₀ * (y / ρ₀ - (i : ℝ)) := by
      field_simp [hρ₀.ne'] <;> ring
    rw [h8]
    have h9 : |ρ₀ * (y / ρ₀ - (i : ℝ))| = ρ₀ * |y / ρ₀ - (i : ℝ)| := by
      rw [abs_mul, abs_of_pos hρ₀] <;> ring
    rw [h9]
    have h10 : ρ₀ * |y / ρ₀ - (i : ℝ)| ≤ ρ₀ * (1 / 2 : ℝ) := by
      gcongr <;> linarith
    linarith
  have h11 : (i : ℝ) ≤ R / ρ₀ + 1 / 2 := by
    have h : (i : ℝ) ≤ z := hi1
    rw [hz_def] at h
    linarith
  have h12 : i ≤ Nat.ceil (R / ρ₀) := by
    have h13 : (i : ℝ) < (Nat.ceil (R / ρ₀) : ℝ) + 1 := by
      have h14 : (R / ρ₀ : ℝ) ≤ (Nat.ceil (R / ρ₀) : ℝ) := Nat.le_ceil _
      linarith
    by_contra h15
    have h16 : i ≥ Nat.ceil (R / ρ₀) + 1 := by linarith
    have h17 : (i : ℝ) ≥ (Nat.ceil (R / ρ₀) : ℝ) + 1 := by exact_mod_cast h16
    linarith
  exact ⟨i, h7, h12⟩

/--
Extract orthogonality and norm facts from an orthonormal triple `(v, e1, e2)`.
-/
lemma orthonormal_triple_facts {v e1 e2 : Point3}
    (h_orth : Orthonormal ℝ (![v, e1, e2] : Fin 3 → Point3)) :
    inner ℝ e1 e2 = 0 ∧ ‖e1‖ = 1 ∧ ‖e2‖ = 1 := by
  let b3 : Fin 3 → Point3 := ![v, e1, e2]
  have h1 : b3 1 = e1 := by simp [b3]
  have h2 : b3 2 = e2 := by simp [b3]
  have hne : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  have h_orth_fn : ∀ (i j : Fin 3), i ≠ j → inner ℝ (b3 i) (b3 j) = 0 := h_orth.2
  have h_raw : inner ℝ (b3 1) (b3 2) = 0 := h_orth_fn 1 2 hne
  have h_orth12 : inner ℝ e1 e2 = 0 := by
    have h4 : inner ℝ e1 e2 = inner ℝ (b3 1) (b3 2) := by
      congr <;> simp [b3]
    rw [h4]; exact h_raw
  have h_norm_e1 : ‖e1‖ = 1 := by
    have h : ‖b3 1‖ = 1 := h_orth.1 1
    rw [h1] at h; exact h
  have h_norm_e2 : ‖e2‖ = 1 := by
    have h : ‖b3 2‖ = 1 := h_orth.1 2
    rw [h2] at h; exact h
  exact ⟨h_orth12, h_norm_e1, h_norm_e2⟩

/--
Pythagorean theorem for two orthonormal vectors `e1, e2` and scalar coefficients `a, b`.
-/
lemma pythagorean_2d {e1 e2 : Point3} {a b : ℝ}
    (h_orth12 : inner ℝ e1 e2 = 0) (h_norm_e1 : ‖e1‖ = 1) (h_norm_e2 : ‖e2‖ = 1) :
    ‖a • e1 + b • e2‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h_inner : inner ℝ (a • e1) (b • e2) = 0 := by
    rw [inner_smul_left, inner_smul_right, h_orth12] <;> ring
  have h_comm : inner ℝ (b • e2) (a • e1) = 0 := by
    rw [real_inner_comm] <;> exact h_inner
  have h_expand : ‖a • e1 + b • e2‖ ^ 2 =
      inner ℝ (a • e1 + b • e2) (a • e1 + b • e2) := by
    exact (inner_self_eq_norm_sq_to_K (a • e1 + b • e2)).symm
  rw [h_expand]
  have h_sum : inner ℝ (a • e1 + b • e2) (a • e1 + b • e2) =
      inner ℝ (a • e1) (a • e1) + inner ℝ (a • e1) (b • e2) +
      inner ℝ (b • e2) (a • e1) + inner ℝ (b • e2) (b • e2) := by
    have h1 : inner ℝ (a • e1 + b • e2) (a • e1 + b • e2) =
        inner ℝ (a • e1) (a • e1 + b • e2) + inner ℝ (b • e2) (a • e1 + b • e2) := by
      rw [inner_add_left] <;> rfl
    rw [h1]
    have h2 : inner ℝ (a • e1) (a • e1 + b • e2) =
        inner ℝ (a • e1) (a • e1) + inner ℝ (a • e1) (b • e2) := by
      rw [inner_add_right] <;> rfl
    have h3 : inner ℝ (b • e2) (a • e1 + b • e2) =
        inner ℝ (b • e2) (a • e1) + inner ℝ (b • e2) (b • e2) := by
      rw [inner_add_right] <;> rfl
    rw [h2, h3] <;> abel
  rw [h_sum, h_inner, h_comm]
  have h_self1 : inner ℝ (a • e1) (a • e1) = ‖a • e1‖ ^ 2 :=
    inner_self_eq_norm_sq_to_K (a • e1)
  have h_self2 : inner ℝ (b • e2) (b • e2) = ‖b • e2‖ ^ 2 :=
    inner_self_eq_norm_sq_to_K (b • e2)
  rw [h_self1, h_self2]
  have h3 : ‖a • e1‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, h_norm_e1]
    simp [Real.norm_eq_abs] <;> ring
  have h4 : ‖b • e2‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, h_norm_e2]
    simp [Real.norm_eq_abs] <;> ring
  rw [h3, h4] <;> ring

end Kakeya.Assouad

end
