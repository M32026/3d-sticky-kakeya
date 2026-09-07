module

/-
# Quantitative Box Theorem

Given a popular dyadic cube Q in parameter space (appears in ≥ c|Y| fibers),
and Y with a Frostman measure of exponent κ and constant C_F, prove that
Q is contained in a box [-R, R]^2 with R = K * (C_F / c)^{1/κ}.

## Main lemmas

1. `frostman_two_far_points` — Frostman non-concentration gives two far-apart directions.
2. `box_bound_from_two_directions` — two directions + approximate incidence → box bound.
3. `quantitative_box_from_popular_cubes` — composed theorem.

## Whiteprint node
`phase0_quantitative_box`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ProductLikeIncidence ENNReal Set Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

private lemma abs_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

private lemma abs_sym (a b : ℝ) : |a - b| = |b - a| := by
  exact abs_sub_comm a b

/-- **Frostman non-concentration: two far-apart points**.

If μ is a Frostman measure with constant C_F and exponent κ, and S ⊆ support μ
is finite nonempty with μ(S) ≥ c > 0, and diam(S) ≥ δ, then there exist
y1, y2 ∈ S with |y1 - y2| ≥ (c / C_F)^{1/κ}. -/
lemma frostman_two_far_points {δ κ C_F c : ℝ}
    {μ : Measure ℝ} {S : Set ℝ}
    (hFrost : IsDirectionFrostman δ κ C_F μ)
    (hS_sub : S ⊆ μ.support)
    (hμS : ENNReal.ofReal c ≤ μ S)
    (hc_pos : 0 < c) (hC_F_pos : 0 < C_F) (hκ_pos : 0 < κ)
    (hS_fin : S.Finite) (hS_nonempty : S.Nonempty)
    (h_diam_ge_delta : δ ≤ (hS_fin.toFinset).max' ((Finite.toFinset_nonempty hS_fin).mpr hS_nonempty) -
           (hS_fin.toFinset).min' ((Finite.toFinset_nonempty hS_fin).mpr hS_nonempty)) :
    ∃ (y1 y2 : ℝ), y1 ∈ S ∧ y2 ∈ S ∧
      |y1 - y2| ≥ (c / C_F) ^ (1 / κ) := by
  let Sf : Finset ℝ := hS_fin.toFinset
  have hSf_nonempty : Sf.Nonempty := (Finite.toFinset_nonempty hS_fin).mpr hS_nonempty
  let a := Sf.min' hSf_nonempty
  let b := Sf.max' hSf_nonempty
  let d := b - a
  have ha_in : a ∈ S := by
    have h : a ∈ Sf := Finset.min'_mem Sf hSf_nonempty
    simpa [Sf] using h
  have hb_in : b ∈ S := by
    have h : b ∈ Sf := Finset.max'_mem Sf hSf_nonempty
    simpa [Sf] using h
  have h_d_nonneg : 0 ≤ d := by
    dsimp only [d]
    have h : a ≤ b := Finset.min'_le Sf b (Finset.max'_mem Sf hSf_nonempty)
    linarith
  have hS_sub_interval : S ⊆ Set.Icc (a - d) (a + d) := by
    intro y hy
    have h2 : y ∈ Sf := by simpa [Sf] using hy
    have h1 : a ≤ y := Finset.min'_le Sf y h2
    have h2' : y ≤ b := Finset.le_max' Sf y h2
    dsimp only [d] at *
    constructor <;> linarith
  have h4 : δ ≤ d := h_diam_ge_delta
  have h5 : d ≤ 1 := by
    have h6 : S ⊆ Set.Icc (0 : ℝ) 1 := hS_sub.trans hFrost.2.1
    have ha0 : 0 ≤ a := (h6 ha_in).1
    have hb1 : b ≤ 1 := (h6 hb_in).2
    dsimp only [d] <;> linarith
  have h6 : μ S ≤ ENNReal.ofReal (C_F * d ^ κ) := by
    have h7 : μ S ≤ μ (Set.Icc (a - d) (a + d)) := measure_mono hS_sub_interval
    have h8 := hFrost.2.2 a d h4 h5
    exact le_trans h7 h8
  have h9 : ENNReal.ofReal c ≤ ENNReal.ofReal (C_F * d ^ κ) := le_trans hμS h6
  have h10 : c ≤ C_F * d ^ κ := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h9
  have h11 : c / C_F ≤ d ^ κ := by
    calc c / C_F
      ≤ (C_F * d ^ κ) / C_F := by gcongr
    _ = d ^ κ := by field_simp [hC_F_pos.ne'] <;> ring
  have h12 : 0 ≤ d := h_d_nonneg
  have h13 : (c / C_F) ^ (1 / κ) ≤ (d ^ κ) ^ (1 / κ) := by gcongr <;> linarith
  have h14 : (d ^ κ) ^ (1 / κ) = d := by
    have h15 : κ * (1 / κ) = 1 := by field_simp [hκ_pos.ne'] <;> ring
    rw [← Real.rpow_mul h12] <;> rw [h15] <;> rw [Real.rpow_one]
  have h16 : (c / C_F) ^ (1 / κ) ≤ d := by
    rw [h14] at h13 <;> exact h13
  have h17 : |a - b| = d := by
    dsimp only [d]
    have h18 : a ≤ b := by linarith [h_d_nonneg]
    rw [abs_of_nonpos (show a - b ≤ 0 by linarith)] <;> linarith
  refine ⟨a, b, ha_in, hb_in, ?_⟩
  rw [h17] <;> exact h16

/-- **Cube coordinate difference bound**. -/
private lemma dyadic_cube_coord_bound {δ : ℝ} {k : Fin 2 → ℤ}
    {p q : EuclideanSpace ℝ (Fin 2)} (i : Fin 2)
    (hp : p ∈ dyadicCube δ k) (hq : q ∈ dyadicCube δ k)
    (hδ_pos : 0 < δ) : |p i - q i| ≤ δ := by
  have h1 : δ * (k i : ℝ) ≤ p i := (hp i).1
  have h2 : p i < δ * ((k i : ℝ) + 1) := (hp i).2
  have h3 : δ * (k i : ℝ) ≤ q i := (hq i).1
  have h4 : q i < δ * ((k i : ℝ) + 1) := (hq i).2
  have h5 : p i - q i ≤ δ := by linarith
  have h6 : -δ ≤ p i - q i := by linarith
  exact abs_le.mpr ⟨h6, h5⟩

/-- **Box bound from two far-apart directions**.

Given a δ-cube Q and two directions y1, y2 with |y1 - y2| ≥ d > 0,
such that for each yi there exist xi ∈ [0,1] and pi ∈ Q with
|xi - (pi0*yi + pi1)| ≤ ε, then for every p ∈ Q:
|p0| ≤ (1 + 2(ε+2δ))/d and |p1| ≤ 1 + (1 + 2(ε+2δ))/d + (ε+2δ). -/
lemma box_bound_from_two_directions {δ ε d : ℝ}
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    {y1 y2 x1 x2 : ℝ}
    {p1 p2 : EuclideanSpace ℝ (Fin 2)}
    (hδ_pos : 0 < δ) (hε_nonneg : 0 ≤ ε)
    (hQ_dyadic : Q ∈ dyadicCubes 2 δ)
    (hy1_in : y1 ∈ Set.Icc (0 : ℝ) 1)
    (hy2_in : y2 ∈ Set.Icc (0 : ℝ) 1)
    (hx1_in : x1 ∈ Set.Icc (0 : ℝ) 1)
    (hx2_in : x2 ∈ Set.Icc (0 : ℝ) 1)
    (hp1_in : p1 ∈ Q) (hp2_in : p2 ∈ Q)
    (h_approx1 : |x1 - (p1 0 * y1 + p1 1)| ≤ ε)
    (h_approx2 : |x2 - (p2 0 * y2 + p2 1)| ≤ ε)
    (hd_pos : 0 < d) (hd_ge : d ≤ |y1 - y2|) :
    ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ Q →
      |p 0| ≤ (1 + 2 * (ε + 2 * δ)) / d ∧
      |p 1| ≤ 1 + (1 + 2 * (ε + 2 * δ)) / d + (ε + 2 * δ) := by
  rcases hQ_dyadic with ⟨k, hQ_eq⟩
  let ε' := ε + 2 * δ
  have hε'_nonneg : 0 ≤ ε' := by linarith
  intro p hp
  have h_diff10 : |p 0 - p1 0| ≤ δ := by
    rw [hQ_eq] at hp hp1_in
    exact dyadic_cube_coord_bound 0 hp hp1_in hδ_pos
  have h_diff11 : |p 1 - p1 1| ≤ δ := by
    rw [hQ_eq] at hp hp1_in
    exact dyadic_cube_coord_bound 1 hp hp1_in hδ_pos
  have h_diff20 : |p 0 - p2 0| ≤ δ := by
    rw [hQ_eq] at hp hp2_in
    exact dyadic_cube_coord_bound 0 hp hp2_in hδ_pos
  have h_diff21 : |p 1 - p2 1| ≤ δ := by
    rw [hQ_eq] at hp hp2_in
    exact dyadic_cube_coord_bound 1 hp hp2_in hδ_pos
  have hy1_abs : |y1| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith [hy1_in.1, hy1_in.2]
  have hy2_abs : |y2| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith [hy2_in.1, hy2_in.2]
  have h_abs_sym1 : |p1 0 - p 0| = |p 0 - p1 0| := abs_sym (p1 0) (p 0)
  have h_abs_sym2 : |p1 1 - p 1| = |p 1 - p1 1| := abs_sym (p1 1) (p 1)
  have h_abs_sym3 : |p2 0 - p 0| = |p 0 - p2 0| := abs_sym (p2 0) (p 0)
  have h_abs_sym4 : |p2 1 - p 1| = |p 1 - p2 1| := abs_sym (p2 1) (p 1)
  have h_bound1 : |(p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)| ≤
      |p1 0 - p 0| * |y1| + |p1 1 - p 1| := by
    have h_eq : (p1 0 * y1 + p1 1) - (p 0 * y1 + p 1) = (p1 0 - p 0) * y1 + (p1 1 - p 1) := by ring
    rw [h_eq]
    have h : |(p1 0 - p 0) * y1 + (p1 1 - p 1)| ≤ |(p1 0 - p 0) * y1| + |p1 1 - p 1| :=
      abs_triangle _ _
    have h2 : |(p1 0 - p 0) * y1| = |p1 0 - p 0| * |y1| := by rw [abs_mul]
    rw [h2] at h
    exact h
  have h_bound2 : |(p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)| ≤
      |p2 0 - p 0| * |y2| + |p2 1 - p 1| := by
    have h_eq : (p2 0 * y2 + p2 1) - (p 0 * y2 + p 1) = (p2 0 - p 0) * y2 + (p2 1 - p 1) := by ring
    rw [h_eq]
    have h : |(p2 0 - p 0) * y2 + (p2 1 - p 1)| ≤ |(p2 0 - p 0) * y2| + |p2 1 - p 1| :=
      abs_triangle _ _
    have h2 : |(p2 0 - p 0) * y2| = |p2 0 - p 0| * |y2| := by rw [abs_mul]
    rw [h2] at h
    exact h
  have h_step1 : |x1 - (p 0 * y1 + p 1)| ≤
      |x1 - (p1 0 * y1 + p1 1)| + |(p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)| := by
    have h_eq : x1 - (p 0 * y1 + p 1) = (x1 - (p1 0 * y1 + p1 1)) + ((p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)) := by ring
    rw [h_eq]
    exact abs_triangle _ _
  have h_approx_p1 : |x1 - (p 0 * y1 + p 1)| ≤ ε' := by
    have h_ybound1 : |p1 0 - p 0| * |y1| ≤ |p 0 - p1 0| := by
      calc |p1 0 - p 0| * |y1|
        = |p 0 - p1 0| * |y1| := by rw [h_abs_sym1]
      _ ≤ |p 0 - p1 0| * 1 := by gcongr
      _ = |p 0 - p1 0| := by ring
    have h_sum1 : |x1 - (p1 0 * y1 + p1 1)| + |(p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)| ≤
        ε + (|p 0 - p1 0| + |p 1 - p1 1|) := by
      have h_a : |x1 - (p1 0 * y1 + p1 1)| ≤ ε := h_approx1
      have h_b : |(p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)| ≤ |p1 0 - p 0| * |y1| + |p1 1 - p 1| := h_bound1
      have h_c : |p1 1 - p 1| = |p 1 - p1 1| := h_abs_sym2
      linarith
    calc |x1 - (p 0 * y1 + p 1)|
      ≤ |x1 - (p1 0 * y1 + p1 1)| + |(p1 0 * y1 + p1 1) - (p 0 * y1 + p 1)| := h_step1
    _ ≤ ε + (|p 0 - p1 0| + |p 1 - p1 1|) := h_sum1
    _ ≤ ε + δ + δ := by
      have h_d1 : |p 0 - p1 0| ≤ δ := h_diff10
      have h_d2 : |p 1 - p1 1| ≤ δ := h_diff11
      linarith
    _ = ε' := by simp [ε'] <;> ring
  have h_step2 : |x2 - (p 0 * y2 + p 1)| ≤
      |x2 - (p2 0 * y2 + p2 1)| + |(p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)| := by
    have h_eq : x2 - (p 0 * y2 + p 1) = (x2 - (p2 0 * y2 + p2 1)) + ((p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)) := by ring
    rw [h_eq]
    exact abs_triangle _ _
  have h_approx_p2 : |x2 - (p 0 * y2 + p 1)| ≤ ε' := by
    have h_ybound2 : |p2 0 - p 0| * |y2| ≤ |p 0 - p2 0| := by
      calc |p2 0 - p 0| * |y2|
        = |p 0 - p2 0| * |y2| := by rw [h_abs_sym3]
      _ ≤ |p 0 - p2 0| * 1 := by gcongr
      _ = |p 0 - p2 0| := by ring
    have h_sum2 : |x2 - (p2 0 * y2 + p2 1)| + |(p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)| ≤
        ε + (|p 0 - p2 0| + |p 1 - p2 1|) := by
      have h_a : |x2 - (p2 0 * y2 + p2 1)| ≤ ε := h_approx2
      have h_b : |(p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)| ≤ |p2 0 - p 0| * |y2| + |p2 1 - p 1| := h_bound2
      have h_c : |p2 1 - p 1| = |p 1 - p2 1| := h_abs_sym4
      linarith
    calc |x2 - (p 0 * y2 + p 1)|
      ≤ |x2 - (p2 0 * y2 + p2 1)| + |(p2 0 * y2 + p2 1) - (p 0 * y2 + p 1)| := h_step2
    _ ≤ ε + (|p 0 - p2 0| + |p 1 - p2 1|) := h_sum2
    _ ≤ ε + δ + δ := by
      have h_d1 : |p 0 - p2 0| ≤ δ := h_diff20
      have h_d2 : |p 1 - p2 1| ≤ δ := h_diff21
      linarith
    _ = ε' := by simp [ε'] <;> ring
  have h_x1x2 : |x1 - x2| ≤ 1 := by
    rw [abs_sub_le_iff] <;> constructor <;> linarith [hx1_in.1, hx1_in.2, hx2_in.1, hx2_in.2]
  let e1 := x1 - (p 0 * y1 + p 1)
  let e2 := x2 - (p 0 * y2 + p 1)
  have h_e1 : |e1| ≤ ε' := h_approx_p1
  have h_e2 : |e2| ≤ ε' := h_approx_p2
  have h_abs_sub : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := fun a b => abs_sub a b
  have h_sub : |p 0 * (y1 - y2)| ≤ |x1 - x2| + 2 * ε' := by
    have h_eq : p 0 * (y1 - y2) = (x1 - x2) - (e1 - e2) := by
      simp only [e1, e2] <;> ring
    rw [h_eq]
    have h1 : |(x1 - x2) - (e1 - e2)| ≤ |x1 - x2| + |e1 - e2| := h_abs_sub _ _
    have h2 : |e1 - e2| ≤ |e1| + |e2| := h_abs_sub _ _
    linarith
  have h_p0_bound : |p 0| * d ≤ 1 + 2 * ε' := by
    have h3 : |p 0 * (y1 - y2)| = |p 0| * |y1 - y2| := by rw [abs_mul]
    have h4 : |p 0| * d ≤ |p 0| * |y1 - y2| :=
      mul_le_mul_of_nonneg_left hd_ge (abs_nonneg _)
    have h6 : |p 0 * (y1 - y2)| ≤ 1 + 2 * ε' := by
      linarith [h_sub, h_x1x2]
    have h5 : |p 0| * |y1 - y2| ≤ 1 + 2 * ε' := by
      rwa [h3] at h6
    exact le_trans h4 h5
  have h_p0 : |p 0| ≤ (1 + 2 * ε') / d := by
    have h : |p 0| * d ≤ 1 + 2 * ε' := h_p0_bound
    calc |p 0|
      = (|p 0| * d) / d := by field_simp [hd_pos.ne'] <;> ring
    _ ≤ ((1 + 2 * ε') / d) := by gcongr
  have h_p1 : |p 1| ≤ 1 + |p 0| + ε' := by
    have hx1_abs : |x1| ≤ 1 := by
      rw [abs_le] <;> constructor <;> linarith [hx1_in.1, hx1_in.2]
    have h_eq : p 1 = x1 - e1 - (p 0 * y1) := by
      simp only [e1] <;> ring
    rw [h_eq]
    have h4 : |x1 - e1 - (p 0 * y1)| ≤ |x1| + |e1| + |p 0 * y1| := by
      have h5 : |x1 - e1 - (p 0 * y1)| ≤ |x1 - e1| + |p 0 * y1| := h_abs_sub _ _
      have h6 : |x1 - e1| ≤ |x1| + |e1| := h_abs_sub _ _
      linarith
    have h7 : |p 0 * y1| = |p 0| * |y1| := by rw [abs_mul]
    calc |x1 - e1 - (p 0 * y1)|
      ≤ |x1| + |e1| + |p 0 * y1| := h4
    _ = |x1| + |e1| + |p 0| * |y1| := by rw [h7]
    _ ≤ 1 + ε' + |p 0| * 1 := by
      gcongr
      <;> linarith [hx1_abs, h_e1, hy1_abs]
    _ = 1 + |p 0| + ε' := by ring
  exact ⟨h_p0, by linarith [h_p1, h_p0]⟩

/-- **Quantitative box theorem from popular cubes**.

Given a δ-dyadic cube Q in parameter space and a finite set S of directions
with Frostman measure μ(S) ≥ c, such that each y ∈ S has an approximate
incidence with some parameter in Q, then every p ∈ Q satisfies
|p0| ≤ A and |p1| ≤ 1 + A + (ε+2δ), where
A = (1 + 2(ε+2δ)) / (c/C_F)^{1/κ}. -/
lemma quantitative_box_from_popular_cubes {δ κ C_F c ε : ℝ}
    {μ : Measure ℝ} {S : Set ℝ}
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ_pos : 0 < δ)
    (hκ_pos : 0 < κ) (hC_F_pos : 0 < C_F) (hc_pos : 0 < c)
    (hε_nonneg : 0 ≤ ε)
    (hFrost : IsDirectionFrostman δ κ C_F μ)
    (hS_sub : S ⊆ μ.support)
    (hμS : ENNReal.ofReal c ≤ μ S)
    (hS_fin : S.Finite) (hS_nonempty : S.Nonempty)
    (h_diam_ge_delta : δ ≤ (hS_fin.toFinset).max' ((Finite.toFinset_nonempty hS_fin).mpr hS_nonempty) - (hS_fin.toFinset).min' ((Finite.toFinset_nonempty hS_fin).mpr hS_nonempty))
    (hQ_dyadic : Q ∈ dyadicCubes 2 δ)
    (h_incidence : ∀ y ∈ S, ∃ (x : ℝ) (p : EuclideanSpace ℝ (Fin 2)),
        x ∈ Set.Icc (0 : ℝ) 1 ∧ p ∈ Q ∧ |x - (p 0 * y + p 1)| ≤ ε) :
    ∀ (p : EuclideanSpace ℝ (Fin 2)), p ∈ Q →
      |p 0| ≤ (1 + 2 * (ε + 2 * δ)) / ((c / C_F) ^ (1 / κ)) ∧
      |p 1| ≤ 1 + (1 + 2 * (ε + 2 * δ)) / ((c / C_F) ^ (1 / κ)) + (ε + 2 * δ) := by
  let d := (c / C_F) ^ (1 / κ)
  have hd_pos : 0 < d := by positivity
  obtain ⟨y1, y2, hy1_in, hy2_in, h_dist⟩ :=
    frostman_two_far_points hFrost hS_sub hμS hc_pos hC_F_pos hκ_pos hS_fin hS_nonempty h_diam_ge_delta
  have h_y1_in_Icc : y1 ∈ Set.Icc (0 : ℝ) 1 := hFrost.2.1 (hS_sub hy1_in)
  have h_y2_in_Icc : y2 ∈ Set.Icc (0 : ℝ) 1 := hFrost.2.1 (hS_sub hy2_in)
  obtain ⟨x1, p1, hx1_in, hp1_in, h_approx1⟩ := h_incidence y1 hy1_in
  obtain ⟨x2, p2, hx2_in, hp2_in, h_approx2⟩ := h_incidence y2 hy2_in
  have hd_ge : d ≤ |y1 - y2| := h_dist
  exact box_bound_from_two_directions hδ_pos hε_nonneg hQ_dyadic
    h_y1_in_Icc h_y2_in_Icc hx1_in hx2_in hp1_in hp2_in h_approx1 h_approx2 hd_pos hd_ge

end ProductLikeIncidence.ProductReduction
