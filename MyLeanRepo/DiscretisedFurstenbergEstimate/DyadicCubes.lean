module

/-
  Dyadic Cubes Infrastructure

  Comprehensive dyadic square infrastructure for the Euclidean plane,
  including covering numbers and comparability with Metric.externalCoveringNumber.

  Main definitions:
  - `DyadicCube n`: half-open square [iδ, (i+1)δ) × [jδ, (j+1)δ), δ = 2^-n
  - `D_nFinset n A`: finite set of level-n cubes intersecting a bounded set
  - `dyadicCoveringNumber n A`: cardinality of D_nFinset

  Main results:
  - `dyadicCoveringNumber_comparable`: external ≤ dyadic ≤ 9 * external
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace DiscretisedFurstenbergEstimate.DyadicCubes

/-- The dyadic scale δ = 2^-n. -/
def dyadicDelta (n : ℕ) : ℝ := 1 / (2 : ℝ)^n

lemma dyadicDelta_pos (n : ℕ) : 0 < dyadicDelta n := by
  rw [dyadicDelta]
  apply div_pos
  · norm_num
  · positivity

lemma dyadicDelta_succ (n : ℕ) : dyadicDelta (n + 1) = dyadicDelta n / 2 := by
  simp [dyadicDelta, pow_succ] <;> field_simp <;> ring

/-- A dyadic cube (square) in ℝ² at level `n`, indexed by `(i, j)`. -/
structure DyadicCube (n : ℕ) : Type where
  i : ℤ
  j : ℤ
  deriving DecidableEq

namespace DyadicCube

variable {n : ℕ}

/-- Side length δ = 2^-n. -/
def side (q : DyadicCube n) : ℝ := dyadicDelta n

lemma side_pos (q : DyadicCube n) : 0 < q.side := dyadicDelta_pos n
lemma side_nonneg (q : DyadicCube n) : 0 ≤ q.side := le_of_lt q.side_pos

/-- Helper to construct a EuclideanPlane point from two coordinates. -/
def mkPoint (x y : ℝ) : EuclideanPlane :=
  WithLp.toLp 2 ![x, y]

lemma mkPoint_apply0 (x y : ℝ) : (mkPoint x y) 0 = x := by simp [mkPoint]
lemma mkPoint_apply1 (x y : ℝ) : (mkPoint x y) 1 = y := by simp [mkPoint]

/-- Lower-left corner. -/
def lower (q : DyadicCube n) : EuclideanPlane :=
  mkPoint ((q.i : ℝ) * q.side) ((q.j : ℝ) * q.side)

/-- The half-open square [iδ, (i+1)δ) × [jδ, (j+1)δ). -/
def toSet (q : DyadicCube n) : Set EuclideanPlane :=
  {x | (q.i : ℝ) * q.side ≤ x 0 ∧ x 0 < ((q.i : ℝ) + 1) * q.side ∧
       (q.j : ℝ) * q.side ≤ x 1 ∧ x 1 < ((q.j : ℝ) + 1) * q.side}

lemma mem_toSet_iff (q : DyadicCube n) (x : EuclideanPlane) :
    x ∈ q.toSet ↔
      (q.i : ℝ) * q.side ≤ x 0 ∧ x 0 < ((q.i : ℝ) + 1) * q.side ∧
      (q.j : ℝ) * q.side ≤ x 1 ∧ x 1 < ((q.j : ℝ) + 1) * q.side := by
  rfl

lemma lower_mem (q : DyadicCube n) : q.lower ∈ q.toSet := by
  rw [mem_toSet_iff]
  have h1 : q.lower 0 = (q.i : ℝ) * q.side := by rw [lower, mkPoint_apply0]
  have h2 : q.lower 1 = (q.j : ℝ) * q.side := by rw [lower, mkPoint_apply1]
  rw [h1, h2]
  have hpos : 0 < q.side := q.side_pos
  exact ⟨le_refl _, by nlinarith, le_refl _, by nlinarith⟩

lemma toSet_nonempty (q : DyadicCube n) : q.toSet.Nonempty :=
  ⟨q.lower, q.lower_mem⟩

/-! ### Distance and diameter -/

lemma dist_le_side_sqrt2 {q : DyadicCube n} {x y : EuclideanPlane}
    (hx : x ∈ q.toSet) (hy : y ∈ q.toSet) :
    dist x y ≤ q.side * Real.sqrt 2 := by
  have hx' := (q.mem_toSet_iff x).mp hx
  have hy' := (q.mem_toSet_iff y).mp hy
  have h1 : |x 0 - y 0| ≤ q.side := by
    rw [abs_le] <;> constructor <;> linarith
  have h2 : |x 1 - y 1| ≤ q.side := by
    rw [abs_le] <;> constructor <;> linarith
  have h3 : ‖x - y‖ ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq (x - y)]
    <;> simp [Fin.sum_univ_two] <;> ring
  have h4 : ‖x - y‖ ^ 2 ≤ 2 * q.side^2 := by
    rw [h3]
    have h5 : (x 0 - y 0)^2 ≤ q.side^2 := by nlinarith [abs_le.mp h1]
    have h6 : (x 1 - y 1)^2 ≤ q.side^2 := by nlinarith [abs_le.mp h2]
    nlinarith
  have h5 : 0 ≤ ‖x - y‖ := by positivity
  have h6 : 0 ≤ q.side := q.side_nonneg
  have h7 : 0 ≤ Real.sqrt 2 := by positivity
  have h8 : (q.side * Real.sqrt 2) ^ 2 = 2 * q.side ^ 2 := by
    calc
      (q.side * Real.sqrt 2) ^ 2
        = q.side ^ 2 * (Real.sqrt 2) ^ 2 := by ring
      _ = q.side ^ 2 * 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
      _ = 2 * q.side ^ 2 := by ring
  have h9 : ‖x - y‖ ^ 2 ≤ (q.side * Real.sqrt 2) ^ 2 := by
    rw [h8] <;> exact h4
  have h10 : 0 ≤ q.side * Real.sqrt 2 := mul_nonneg h6 h7
  have h11 : - (q.side * Real.sqrt 2) ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ q.side * Real.sqrt 2 :=
    abs_le_of_sq_le_sq' h9 h10
  exact h11.2

lemma diam_le (q : DyadicCube n) :
    EMetric.diam q.toSet ≤ ENNReal.ofReal (q.side * Real.sqrt 2) := by
  apply EMetric.diam_le
  intro x hx y hy
  have h : dist x y ≤ q.side * Real.sqrt 2 := dist_le_side_sqrt2 hx hy
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h

/-- Each coordinate of a Euclidean plane point is bounded by its norm. -/
lemma coord_abs_le_norm (z : EuclideanPlane) (k : Fin 2) : |z k| ≤ ‖z‖ := by
  have h1 : |z k| ^ 2 ≤ ‖z‖ ^ 2 := by
    have h2 : ‖z‖ ^ 2 = ∑ i : Fin 2, |z i| ^ 2 := by
      have h_norm : ‖z‖ = Real.sqrt (∑ i : Fin 2, (z i)^2) := by
        simpa [EuclideanSpace.norm_eq] using rfl
      have h_nonneg : 0 ≤ ∑ i : Fin 2, (z i)^2 := by positivity
      have h3 : ‖z‖ ^ 2 = ∑ i : Fin 2, (z i)^2 := by
        rw [h_norm, Real.sq_sqrt h_nonneg]
      have h4 : ∑ i : Fin 2, (z i)^2 = ∑ i : Fin 2, |z i|^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sq_abs]
      rw [h3, h4]
    rw [h2]
    have h3 : |z k| ^ 2 ≤ ∑ i : Fin 2, |z i| ^ 2 := by
      apply Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_univ k)
    exact h3
  have h4 : 0 ≤ |z k| := by positivity
  have h5 : 0 ≤ ‖z‖ := by positivity
  nlinarith [sq_nonneg (|z k| - ‖z‖)]


/-! ### Disjointness -/

lemma disjoint_of_ne {q₁ q₂ : DyadicCube n} (hne : q₁ ≠ q₂) :
    Disjoint q₁.toSet q₂.toSet := by
  have h : q₁.i ≠ q₂.i ∨ q₁.j ≠ q₂.j := by
    by_contra h'
    push Not at h'
    have h3 : q₁ = q₂ := by
      cases q₁ <;> cases q₂ <;> simp_all
    exact hne h3
  rcases h with (h | h)
  · -- i coordinates differ
    by_cases hlt : q₁.i < q₂.i
    · have h4 : (q₁.i + 1 : ℤ) ≤ q₂.i := by linarith
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h5 : x 0 < ((q₁.i : ℝ) + 1) * q₁.side := (q₁.mem_toSet_iff x).mp hx1 |>.2.1
      have h6 : (q₂.i : ℝ) * q₂.side ≤ x 0 := (q₂.mem_toSet_iff x).mp hx2 |>.1
      have hside : q₁.side = q₂.side := rfl
      have h7 : ((q₁.i : ℝ) + 1) * q₁.side ≤ (q₂.i : ℝ) * q₂.side := by
        have h8 : (q₁.i : ℝ) + 1 ≤ (q₂.i : ℝ) := by exact_mod_cast h4
        calc ((q₁.i : ℝ) + 1) * q₁.side
          ≤ (q₂.i : ℝ) * q₁.side := by gcongr <;> exact q₁.side_nonneg
        _ = (q₂.i : ℝ) * q₂.side := by rw [hside]
      linarith
    · have hlt' : q₂.i < q₁.i := by omega
      have h4 : (q₂.i + 1 : ℤ) ≤ q₁.i := by linarith
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h5 : x 0 < ((q₂.i : ℝ) + 1) * q₂.side := (q₂.mem_toSet_iff x).mp hx2 |>.2.1
      have h6 : (q₁.i : ℝ) * q₁.side ≤ x 0 := (q₁.mem_toSet_iff x).mp hx1 |>.1
      have hside : q₁.side = q₂.side := rfl
      have h7 : ((q₂.i : ℝ) + 1) * q₂.side ≤ (q₁.i : ℝ) * q₁.side := by
        have h8 : (q₂.i : ℝ) + 1 ≤ (q₁.i : ℝ) := by exact_mod_cast h4
        calc ((q₂.i : ℝ) + 1) * q₂.side
          ≤ (q₁.i : ℝ) * q₂.side := by gcongr <;> exact q₂.side_nonneg
        _ = (q₁.i : ℝ) * q₁.side := by rw [hside]
      linarith
  · -- j coordinates differ
    by_cases hlt : q₁.j < q₂.j
    · have h4 : (q₁.j + 1 : ℤ) ≤ q₂.j := by linarith
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h5 : x 1 < ((q₁.j : ℝ) + 1) * q₁.side := (q₁.mem_toSet_iff x).mp hx1 |>.2.2.2
      have h6 : (q₂.j : ℝ) * q₂.side ≤ x 1 := (q₂.mem_toSet_iff x).mp hx2 |>.2.2.1
      have hside : q₁.side = q₂.side := rfl
      have h7 : ((q₁.j : ℝ) + 1) * q₁.side ≤ (q₂.j : ℝ) * q₂.side := by
        have h8 : (q₁.j : ℝ) + 1 ≤ (q₂.j : ℝ) := by exact_mod_cast h4
        calc ((q₁.j : ℝ) + 1) * q₁.side
          ≤ (q₂.j : ℝ) * q₁.side := by gcongr <;> exact q₁.side_nonneg
        _ = (q₂.j : ℝ) * q₂.side := by rw [hside]
      linarith
    · have hlt' : q₂.j < q₁.j := by omega
      have h4 : (q₂.j + 1 : ℤ) ≤ q₁.j := by linarith
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h5 : x 1 < ((q₂.j : ℝ) + 1) * q₂.side := (q₂.mem_toSet_iff x).mp hx2 |>.2.2.2
      have h6 : (q₁.j : ℝ) * q₁.side ≤ x 1 := (q₁.mem_toSet_iff x).mp hx1 |>.2.2.1
      have hside : q₁.side = q₂.side := rfl
      have h7 : ((q₂.j : ℝ) + 1) * q₂.side ≤ (q₁.j : ℝ) * q₁.side := by
        have h8 : (q₂.j : ℝ) + 1 ≤ (q₁.j : ℝ) := by exact_mod_cast h4
        calc ((q₂.j : ℝ) + 1) * q₂.side
          ≤ (q₁.j : ℝ) * q₂.side := by gcongr <;> exact q₂.side_nonneg
        _ = (q₁.j : ℝ) * q₁.side := by rw [hside]
      linarith

/-! ### Covering property -/

lemma cover (n : ℕ) :
    (⋃ (i : ℤ), ⋃ (j : ℤ), (⟨i, j⟩ : DyadicCube n).toSet) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  let δ := dyadicDelta n
  have hδ : 0 < δ := dyadicDelta_pos n
  have h1 : ∃ (i : ℤ), (i : ℝ) * δ ≤ x 0 ∧ x 0 < ((i : ℝ) + 1) * δ := by
    refine ⟨⌊x 0 / δ⌋, ?_⟩
    have h2 : (⌊x 0 / δ⌋ : ℝ) ≤ x 0 / δ := Int.floor_le _
    have h3 : x 0 / δ < (⌊x 0 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · calc (⌊x 0 / δ⌋ : ℝ) * δ ≤ (x 0 / δ) * δ := by gcongr
        _ = x 0 := by field_simp [hδ.ne'] <;> ring
    · calc x 0 = (x 0 / δ) * δ := by field_simp [hδ.ne'] <;> ring
        _ < ((⌊x 0 / δ⌋ : ℝ) + 1) * δ := by gcongr
  have h2 : ∃ (j : ℤ), (j : ℝ) * δ ≤ x 1 ∧ x 1 < ((j : ℝ) + 1) * δ := by
    refine ⟨⌊x 1 / δ⌋, ?_⟩
    have h2' : (⌊x 1 / δ⌋ : ℝ) ≤ x 1 / δ := Int.floor_le _
    have h3' : x 1 / δ < (⌊x 1 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · calc (⌊x 1 / δ⌋ : ℝ) * δ ≤ (x 1 / δ) * δ := by gcongr
        _ = x 1 := by field_simp [hδ.ne'] <;> ring
    · calc x 1 = (x 1 / δ) * δ := by field_simp [hδ.ne'] <;> ring
        _ < ((⌊x 1 / δ⌋ : ℝ) + 1) * δ := by gcongr
  rcases h1 with ⟨i, hi1, hi2⟩
  rcases h2 with ⟨j, hj1, hj2⟩
  have h3 : x ∈ (⟨i, j⟩ : DyadicCube n).toSet := by
    rw [mem_toSet_iff] <;> exact ⟨hi1, hi2, hj1, hj2⟩
  exact ⟨i, j, h3⟩

/-! ### Children and parent -/

/-- The four children at level n+1. -/
def children (q : DyadicCube n) : Finset (DyadicCube (n + 1)) :=
  let c1 : DyadicCube (n + 1) := ⟨2 * q.i, 2 * q.j⟩
  let c2 : DyadicCube (n + 1) := ⟨2 * q.i + 1, 2 * q.j⟩
  let c3 : DyadicCube (n + 1) := ⟨2 * q.i, 2 * q.j + 1⟩
  let c4 : DyadicCube (n + 1) := ⟨2 * q.i + 1, 2 * q.j + 1⟩
  insert c1 (insert c2 (insert c3 {c4}))

lemma children_card (q : DyadicCube n) : q.children.card = 4 := by
  simp [children] <;> decide

/-- Parent at level n-1. -/
def parent {n : ℕ} (q : DyadicCube (n + 1)) : DyadicCube n :=
  ⟨q.i / 2, q.j / 2⟩

lemma parent_eq {n : ℕ} (q : DyadicCube n) (c : DyadicCube (n + 1))
    (hc : c ∈ q.children) : c.parent = q := by
  simp only [children, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with (rfl | rfl | rfl | rfl)
  · cases q with | mk i j => simp [parent] <;> congr <;> omega
  · cases q with | mk i j => simp [parent] <;> congr <;> omega
  · cases q with | mk i j => simp [parent] <;> congr <;> omega
  · cases q with | mk i j => simp [parent] <;> congr <;> omega

lemma parent_toSet {n : ℕ} (q : DyadicCube (n + 1)) :
    q.toSet ⊆ q.parent.toSet := by
  intro x hx
  have hx' := (q.mem_toSet_iff x).mp hx
  set δ' := dyadicDelta (n + 1) with hδ'
  have hδ : dyadicDelta n = 2 * δ' := by
    have h : dyadicDelta (n + 1) = dyadicDelta n / 2 := dyadicDelta_succ n
    have h2 : δ' = dyadicDelta n / 2 := by simpa [hδ'] using h
    linarith
  have hpos : 0 ≤ δ' := le_of_lt (dyadicDelta_pos (n + 1))
  have h_i1 : (q.parent.i : ℝ) * 2 ≤ (q.i : ℝ) := by
    have h : (q.i / 2 : ℤ) * 2 ≤ q.i := by omega
    have h' : ((q.i / 2 : ℤ) : ℝ) * 2 ≤ (q.i : ℝ) := by exact_mod_cast h
    simpa [parent] using h'
  have h_i2 : (q.i : ℝ) + 1 ≤ ((q.parent.i : ℝ) + 1) * 2 := by
    have h : q.i + 1 ≤ (q.i / 2 : ℤ) * 2 + 2 := by omega
    have h' : (q.i : ℝ) + 1 ≤ ((q.i / 2 : ℤ) : ℝ) * 2 + 2 := by exact_mod_cast h
    have h'' : ((q.i / 2 : ℤ) : ℝ) * 2 + 2 = (((q.i / 2 : ℤ) : ℝ) + 1) * 2 := by ring
    have h3 : (q.i : ℝ) + 1 ≤ (((q.i / 2 : ℤ) : ℝ) + 1) * 2 := by
      calc (q.i : ℝ) + 1 ≤ ((q.i / 2 : ℤ) : ℝ) * 2 + 2 := h'
        _ = (((q.i / 2 : ℤ) : ℝ) + 1) * 2 := h''
    simpa [parent] using h3
  have h_j1 : (q.parent.j : ℝ) * 2 ≤ (q.j : ℝ) := by
    have h : (q.j / 2 : ℤ) * 2 ≤ q.j := by omega
    have h' : ((q.j / 2 : ℤ) : ℝ) * 2 ≤ (q.j : ℝ) := by exact_mod_cast h
    simpa [parent] using h'
  have h_j2 : (q.j : ℝ) + 1 ≤ ((q.parent.j : ℝ) + 1) * 2 := by
    have h : q.j + 1 ≤ (q.j / 2 : ℤ) * 2 + 2 := by omega
    have h' : (q.j : ℝ) + 1 ≤ ((q.j / 2 : ℤ) : ℝ) * 2 + 2 := by exact_mod_cast h
    have h'' : ((q.j / 2 : ℤ) : ℝ) * 2 + 2 = (((q.j / 2 : ℤ) : ℝ) + 1) * 2 := by ring
    have h3 : (q.j : ℝ) + 1 ≤ (((q.j / 2 : ℤ) : ℝ) + 1) * 2 := by
      calc (q.j : ℝ) + 1 ≤ ((q.j / 2 : ℤ) : ℝ) * 2 + 2 := h'
        _ = (((q.j / 2 : ℤ) : ℝ) + 1) * 2 := h''
    simpa [parent] using h3
  rw [q.parent.mem_toSet_iff]
  simp only [parent, side]
  rw [hδ]
  exact ⟨
    calc (q.parent.i : ℝ) * (2 * δ')
      = ((q.parent.i : ℝ) * 2) * δ' := by ring
    _ ≤ (q.i : ℝ) * δ' := mul_le_mul_of_nonneg_right h_i1 hpos
    _ ≤ x 0 := hx'.1,
    calc x 0
      < ((q.i : ℝ) + 1) * δ' := hx'.2.1
    _ ≤ (((q.parent.i : ℝ) + 1) * 2) * δ' := mul_le_mul_of_nonneg_right h_i2 hpos
    _ = ((q.parent.i : ℝ) + 1) * (2 * δ') := by ring,
    calc (q.parent.j : ℝ) * (2 * δ')
      = ((q.parent.j : ℝ) * 2) * δ' := by ring
    _ ≤ (q.j : ℝ) * δ' := mul_le_mul_of_nonneg_right h_j1 hpos
    _ ≤ x 1 := hx'.2.2.1,
    calc x 1
      < ((q.j : ℝ) + 1) * δ' := hx'.2.2.2
    _ ≤ (((q.parent.j : ℝ) + 1) * 2) * δ' := mul_le_mul_of_nonneg_right h_j2 hpos
    _ = ((q.parent.j : ℝ) + 1) * (2 * δ') := by ring
  ⟩

/-- Helper for children_cover: lower-half child interval. -/
lemma child_interval_lo (i : ℤ) (x : ℝ) (δ : ℝ)
    (hlo : (i : ℝ) * δ ≤ x) (hmid : x < (i : ℝ) * δ + δ / 2) :
    (2 * (i : ℝ)) * (δ / 2) ≤ x ∧ x < (2 * (i : ℝ) + 1) * (δ / 2) := by
  have h1 : (2 * (i : ℝ)) * (δ / 2) = (i : ℝ) * δ := by ring
  have h2 : (i : ℝ) * δ + δ / 2 = (2 * (i : ℝ) + 1) * (δ / 2) := by ring
  exact ⟨by rw [h1]; exact hlo, by rw [h2] at hmid; exact hmid⟩

/-- Helper for children_cover: upper-half child interval. -/
lemma child_interval_hi (i : ℤ) (x : ℝ) (δ : ℝ)
    (hhi : x < ((i : ℝ) + 1) * δ) (hmid : (i : ℝ) * δ + δ / 2 ≤ x) :
    (2 * (i : ℝ) + 1) * (δ / 2) ≤ x ∧ x < (2 * (i : ℝ) + 2) * (δ / 2) := by
  have h1 : (i : ℝ) * δ + δ / 2 = (2 * (i : ℝ) + 1) * (δ / 2) := by ring
  have h2 : ((i : ℝ) + 1) * δ = (2 * (i : ℝ) + 2) * (δ / 2) := by ring
  exact ⟨by rw [h1] at hmid; exact hmid, by rw [h2] at hhi; exact hhi⟩

lemma children_cover (q : DyadicCube n) :
    q.toSet = ⋃ c ∈ q.children, c.toSet := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    have hx' := (q.mem_toSet_iff x).mp hx
    let δ := dyadicDelta n
    have hδ_pos : 0 < δ := dyadicDelta_pos n
    have hδ2 : dyadicDelta (n + 1) = δ / 2 := dyadicDelta_succ n
    have h_xmid : x 0 < (q.i : ℝ) * δ + δ / 2 ∨ (q.i : ℝ) * δ + δ / 2 ≤ x 0 := by
      by_cases h : x 0 < (q.i : ℝ) * δ + δ / 2
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have h_ymid : x 1 < (q.j : ℝ) * δ + δ / 2 ∨ (q.j : ℝ) * δ + δ / 2 ≤ x 1 := by
      by_cases h : x 1 < (q.j : ℝ) * δ + δ / 2
      · exact Or.inl h
      · exact Or.inr (by linarith)
    by_cases h_xmid : x 0 < (q.i : ℝ) * δ + δ / 2
    · -- x 0 < mid
      by_cases h_ymid : x 1 < (q.j : ℝ) * δ + δ / 2
      · -- child (2i, 2j)
        let c : DyadicCube (n + 1) := ⟨2 * q.i, 2 * q.j⟩
        have hc : c ∈ q.children := by dsimp only [c]; simp [children] <;> decide
        have h0 := child_interval_lo q.i (x 0) δ hx'.1 h_xmid
        have h1 := child_interval_lo q.j (x 1) δ hx'.2.2.1 h_ymid
        have h_goal : x ∈ c.toSet := by
          rw [c.mem_toSet_iff]
          have hsi : c.side = δ / 2 := by simp [side, hδ2]
          rw [hsi]
          simp [c] <;> exact ⟨h0.1, by linarith [h0.2], h1.1, by linarith [h1.2]⟩
        exact ⟨c, hc, h_goal⟩
      · -- child (2i, 2j+1)
        have h_ymid' : (q.j : ℝ) * δ + δ / 2 ≤ x 1 := by linarith
        let c : DyadicCube (n + 1) := ⟨2 * q.i, 2 * q.j + 1⟩
        have hc : c ∈ q.children := by dsimp only [c]; simp [children] <;> decide
        have h0 := child_interval_lo q.i (x 0) δ hx'.1 h_xmid
        have h1 := child_interval_hi q.j (x 1) δ hx'.2.2.2 h_ymid'
        have h_goal : x ∈ c.toSet := by
          rw [c.mem_toSet_iff]
          have hsi : c.side = δ / 2 := by simp [side, hδ2]
          rw [hsi]
          simp [c] <;> exact ⟨h0.1, by linarith [h0.2], h1.1, by linarith [h1.2]⟩
        exact ⟨c, hc, h_goal⟩
    · -- x 0 ≥ mid
      have h_xmid' : (q.i : ℝ) * δ + δ / 2 ≤ x 0 := by linarith
      by_cases h_ymid : x 1 < (q.j : ℝ) * δ + δ / 2
      · -- child (2i+1, 2j)
        let c : DyadicCube (n + 1) := ⟨2 * q.i + 1, 2 * q.j⟩
        have hc : c ∈ q.children := by dsimp only [c]; simp [children] <;> decide
        have h0 := child_interval_hi q.i (x 0) δ hx'.2.1 h_xmid'
        have h1 := child_interval_lo q.j (x 1) δ hx'.2.2.1 h_ymid
        have h_goal : x ∈ c.toSet := by
          rw [c.mem_toSet_iff]
          have hsi : c.side = δ / 2 := by simp [side, hδ2]
          rw [hsi]
          simp [c] <;> exact ⟨h0.1, by linarith [h0.2], h1.1, by linarith [h1.2]⟩
        exact ⟨c, hc, h_goal⟩
      · -- child (2i+1, 2j+1)
        have h_ymid' : (q.j : ℝ) * δ + δ / 2 ≤ x 1 := by linarith
        let c : DyadicCube (n + 1) := ⟨2 * q.i + 1, 2 * q.j + 1⟩
        have hc : c ∈ q.children := by dsimp only [c]; simp [children] <;> decide
        have h0 := child_interval_hi q.i (x 0) δ hx'.2.1 h_xmid'
        have h1 := child_interval_hi q.j (x 1) δ hx'.2.2.2 h_ymid'
        have h_goal : x ∈ c.toSet := by
          rw [c.mem_toSet_iff]
          have hsi : c.side = δ / 2 := by simp [side, hδ2]
          rw [hsi]
          simp [c] <;> exact ⟨h0.1, by linarith [h0.2], h1.1, by linarith [h1.2]⟩
        exact ⟨c, hc, h_goal⟩
  · rintro ⟨c, hc, hxc⟩
    have hsub : c.toSet ⊆ c.parent.toSet := parent_toSet c
    have hpar : c.parent = q := parent_eq q c hc
    rw [hpar] at hsub
    exact hsub hxc


/-! ### Ball covering bound -/

lemma ball_intersects_finite (x : EuclideanPlane) {r : ℝ} (hr : 0 ≤ r) :
    Set.Finite {q : DyadicCube n | (q.toSet ∩ Metric.closedBall x r).Nonempty} := by
  let δ := dyadicDelta n
  have hδ : 0 < δ := dyadicDelta_pos n
  let i_lo : ℤ := ⌊(x 0 - r) / δ - 1⌋
  let i_hi : ℤ := ⌈(x 0 + r) / δ⌉
  let j_lo : ℤ := ⌊(x 1 - r) / δ - 1⌋
  let j_hi : ℤ := ⌈(x 1 + r) / δ⌉
  have h_bounds : ∀ (q : DyadicCube n), (q.toSet ∩ Metric.closedBall x r).Nonempty →
      i_lo ≤ q.i ∧ q.i ≤ i_hi ∧ j_lo ≤ q.j ∧ q.j ≤ j_hi := by
    intro q hq
    rcases hq with ⟨y, hy_q, hy_ball⟩
    have h_yq := (q.mem_toSet_iff y).mp hy_q
    have h_dist : dist y x ≤ r := (Metric.mem_closedBall).mp hy_ball
    have h_coord0 : |y 0 - x 0| ≤ dist y x := coord_abs_le_norm (y - x) 0
    have h_coord1 : |y 1 - x 1| ≤ dist y x := coord_abs_le_norm (y - x) 1
    have h_y0_lo : x 0 - r ≤ y 0 := by
      have h : |y 0 - x 0| ≤ r := h_coord0.trans h_dist
      linarith [abs_le.mp h]
    have h_y0_hi : y 0 ≤ x 0 + r := by
      have h : |y 0 - x 0| ≤ r := h_coord0.trans h_dist
      linarith [abs_le.mp h]
    have h_y1_lo : x 1 - r ≤ y 1 := by
      have h : |y 1 - x 1| ≤ r := h_coord1.trans h_dist
      linarith [abs_le.mp h]
    have h_y1_hi : y 1 ≤ x 1 + r := by
      have h : |y 1 - x 1| ≤ r := h_coord1.trans h_dist
      linarith [abs_le.mp h]
    have h_i_hi : (q.i : ℝ) ≤ (x 0 + r) / δ := by
      have h : (q.i : ℝ) * δ ≤ y 0 := h_yq.1
      have h' : (q.i : ℝ) * δ ≤ x 0 + r := by linarith
      calc (q.i : ℝ)
        = ((q.i : ℝ) * δ) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (x 0 + r) / δ := by gcongr
    have h_i_lo : (x 0 - r) / δ - 1 < (q.i : ℝ) := by
      have h : y 0 < ((q.i : ℝ) + 1) * δ := h_yq.2.1
      have h' : x 0 - r < ((q.i : ℝ) + 1) * δ := by linarith
      have h'' : (x 0 - r) / δ < (q.i : ℝ) + 1 := by
        calc (x 0 - r) / δ
          < (((q.i : ℝ) + 1) * δ) / δ := by gcongr
        _ = (q.i : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      linarith
    have h_j_hi : (q.j : ℝ) ≤ (x 1 + r) / δ := by
      have h : (q.j : ℝ) * δ ≤ y 1 := h_yq.2.2.1
      have h' : (q.j : ℝ) * δ ≤ x 1 + r := by linarith
      calc (q.j : ℝ)
        = ((q.j : ℝ) * δ) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (x 1 + r) / δ := by gcongr
    have h_j_lo : (x 1 - r) / δ - 1 < (q.j : ℝ) := by
      have h : y 1 < ((q.j : ℝ) + 1) * δ := h_yq.2.2.2
      have h' : x 1 - r < ((q.j : ℝ) + 1) * δ := by linarith
      have h'' : (x 1 - r) / δ < (q.j : ℝ) + 1 := by
        calc (x 1 - r) / δ
          < (((q.j : ℝ) + 1) * δ) / δ := by gcongr
        _ = (q.j : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      linarith
    have h_i_lo' : i_lo ≤ q.i := by
      have h_floor : (i_lo : ℝ) ≤ (x 0 - r) / δ - 1 := Int.floor_le _
      have h : (i_lo : ℝ) < (q.i : ℝ) := by linarith
      have h' : i_lo ≤ q.i := by exact_mod_cast (le_of_lt h)
      exact h'
    have h_i_hi' : q.i ≤ i_hi := by
      have h_ceil : (x 0 + r) / δ ≤ (i_hi : ℝ) := Int.le_ceil _
      have h : (q.i : ℝ) ≤ (i_hi : ℝ) := by linarith
      exact_mod_cast h
    have h_j_lo' : j_lo ≤ q.j := by
      have h_floor : (j_lo : ℝ) ≤ (x 1 - r) / δ - 1 := Int.floor_le _
      have h : (j_lo : ℝ) < (q.j : ℝ) := by linarith
      have h' : j_lo ≤ q.j := by exact_mod_cast (le_of_lt h)
      exact h'
    have h_j_hi' : q.j ≤ j_hi := by
      have h_ceil : (x 1 + r) / δ ≤ (j_hi : ℝ) := Int.le_ceil _
      have h : (q.j : ℝ) ≤ (j_hi : ℝ) := by linarith
      exact_mod_cast h
    exact ⟨h_i_lo', h_i_hi', h_j_lo', h_j_hi'⟩
  let S : Finset (DyadicCube n) := (Finset.Icc i_lo i_hi).biUnion fun i =>
    (Finset.Icc j_lo j_hi).image fun j => (⟨i, j⟩ : DyadicCube n)
  have h_subset : {q : DyadicCube n | (q.toSet ∩ Metric.closedBall x r).Nonempty} ⊆ (S : Set (DyadicCube n)) := by
    intro q hq
    have h_b := h_bounds q hq
    simp only [S, Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨q.i, Finset.mem_Icc.mpr ⟨h_b.1, h_b.2.1⟩, ?_⟩
    simp only [Finset.mem_image]
    refine ⟨q.j, Finset.mem_Icc.mpr ⟨h_b.2.2.1, h_b.2.2.2⟩, ?_⟩
    cases q <;> rfl
  exact Set.Finite.subset (Finset.finite_toSet S) h_subset

/-- Center of the cube. -/
def center (q : DyadicCube n) : EuclideanPlane :=
  mkPoint (((q.i : ℝ) + 1 / 2) * q.side) (((q.j : ℝ) + 1 / 2) * q.side)

lemma center_apply (q : DyadicCube n) :
    q.center 0 = ((q.i : ℝ) + 1 / 2) * q.side ∧
    q.center 1 = ((q.j : ℝ) + 1 / 2) * q.side := by
  constructor
  · rw [center, mkPoint_apply0]
  · rw [center, mkPoint_apply1]

lemma dist_center_le {q : DyadicCube n} {x : EuclideanPlane} (hx : x ∈ q.toSet) :
    dist x q.center ≤ q.side := by
  have hx' := (q.mem_toSet_iff x).mp hx
  have hc := q.center_apply
  have h1 : |x 0 - q.center 0| ≤ q.side / 2 := by
    rw [hc.1, abs_le] <;> constructor <;> linarith
  have h2 : |x 1 - q.center 1| ≤ q.side / 2 := by
    rw [hc.2, abs_le] <;> constructor <;> linarith
  have h3 : ‖x - q.center‖ ^ 2 = (x 0 - q.center 0)^2 + (x 1 - q.center 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq (x - q.center)]
    <;> simp [Fin.sum_univ_two] <;> ring
  have h4 : (x 0 - q.center 0)^2 ≤ (q.side / 2)^2 := by
    have h5 : |x 0 - q.center 0| ≤ q.side / 2 := h1
    have h6 : (x 0 - q.center 0)^2 = |x 0 - q.center 0|^2 := by rw [sq_abs]
    rw [h6]
    gcongr <;> linarith
  have h7 : (x 1 - q.center 1)^2 ≤ (q.side / 2)^2 := by
    have h8 : |x 1 - q.center 1| ≤ q.side / 2 := h2
    have h9 : (x 1 - q.center 1)^2 = |x 1 - q.center 1|^2 := by rw [sq_abs]
    rw [h9]
    gcongr <;> linarith
  have h10 : ‖x - q.center‖ ^ 2 ≤ q.side ^ 2 / 2 := by
    rw [h3]
    nlinarith
  have h11 : ‖x - q.center‖ ^ 2 ≤ q.side ^ 2 := by
    nlinarith [q.side_nonneg]
  have h12 : 0 ≤ ‖x - q.center‖ := by positivity
  have h13 : 0 ≤ q.side := q.side_nonneg
  have h14 : ‖x - q.center‖ ≤ q.side := by
    by_contra h
    have h15 : q.side < ‖x - q.center‖ := by linarith
    have h16 : q.side ^ 2 < ‖x - q.center‖ ^ 2 := by nlinarith
    linarith
  have hdist : dist x q.center = ‖x - q.center‖ := by
    simp [dist_eq_norm]
  rw [hdist]
  exact h14


end DyadicCube

/-! ### Dyadic covering number (explicit n parameter) -/

/-- Set of level-n cubes intersecting A. -/
def D_nSet (n : ℕ) (A : Set EuclideanPlane) : Set (DyadicCube n) :=
  {q | (q.toSet ∩ A).Nonempty}

/-- Bounded sets intersect finitely many dyadic cubes. -/
lemma D_nSet_finite (n : ℕ) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) : Set.Finite (D_nSet n A) := by
  have h1 : ∃ (r : ℝ), A ⊆ Metric.ball (0 : EuclideanPlane) r := hA.subset_ball 0
  rcases h1 with ⟨r, hsub⟩
  let R : ℝ := max r 0
  have hR_nonneg : 0 ≤ R := le_max_right r 0
  have hsub' : A ⊆ Metric.closedBall (0 : EuclideanPlane) R := by
    intro x hx
    have hball : x ∈ Metric.ball (0 : EuclideanPlane) r := hsub hx
    have hdist : dist x 0 < r := Metric.mem_ball.mp hball
    have h : dist x 0 ≤ R := by
      have h2 : r ≤ R := le_max_left r 0
      linarith
    exact Metric.mem_closedBall.mpr h
  have h2 : D_nSet n A ⊆ {q : DyadicCube n | (q.toSet ∩ Metric.closedBall (0 : EuclideanPlane) R).Nonempty} := by
    intro q hq
    simp only [D_nSet, Set.mem_setOf_eq] at hq ⊢
    exact hq.mono (Set.inter_subset_inter_right _ hsub')
  exact Set.Finite.subset (DyadicCube.ball_intersects_finite (n := n) (0 : EuclideanPlane) hR_nonneg) h2


/-- Finite set of level-n cubes intersecting a bounded set A. -/
def D_nFinset (n : ℕ) (A : Set EuclideanPlane)
    (hA : Bornology.IsBounded A) : Finset (DyadicCube n) :=
  (D_nSet_finite n hA).toFinset

lemma D_nFinset_mem (n : ℕ) {A : Set EuclideanPlane}
    {hA : Bornology.IsBounded A} {q : DyadicCube n} :
    q ∈ D_nFinset n A hA ↔ (q.toSet ∩ A).Nonempty := by
  simp [D_nFinset, D_nSet, Set.Finite.mem_toFinset]
  <;> rfl

/-- Number of level-n cubes intersecting A. -/
def dyadicCoveringNumber (n : ℕ) (A : Set EuclideanPlane)
    (hA : Bornology.IsBounded A) : ℕ :=
  (D_nFinset n A hA).card

/-! ### Comparability with externalCoveringNumber -/

/-- At most 9 dyadic cubes of side δ intersect a closed ball of radius δ. -/
lemma ball_9_cubes (n : ℕ) (c : EuclideanPlane) :
    (D_nSet_finite n (A := Metric.closedBall c (dyadicDelta n))
      Metric.isBounded_closedBall).toFinset.card ≤ 9 := by
  let δ := dyadicDelta n
  have hδ : 0 < δ := dyadicDelta_pos n
  let i0 : ℤ := ⌊c 0 / δ⌋
  let j0 : ℤ := ⌊c 1 / δ⌋
  have h_i01 : (i0 : ℝ) * δ ≤ c 0 := by
    have h : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le _
    calc (i0 : ℝ) * δ ≤ (c 0 / δ) * δ := by gcongr
      _ = c 0 := by field_simp [hδ.ne'] <;> ring
  have h_i02 : c 0 < ((i0 : ℝ) + 1) * δ := by
    have h : c 0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one _
    calc c 0 = (c 0 / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ < (((i0 : ℝ) + 1) * δ) := by gcongr
  have h_j01 : (j0 : ℝ) * δ ≤ c 1 := by
    have h : (j0 : ℝ) ≤ c 1 / δ := Int.floor_le _
    calc (j0 : ℝ) * δ ≤ (c 1 / δ) * δ := by gcongr
      _ = c 1 := by field_simp [hδ.ne'] <;> ring
  have h_j02 : c 1 < ((j0 : ℝ) + 1) * δ := by
    have h : c 1 / δ < (j0 : ℝ) + 1 := Int.lt_floor_add_one _
    calc c 1 = (c 1 / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ < (((j0 : ℝ) + 1) * δ) := by gcongr
  have h_bounds : ∀ (q : DyadicCube n),
      (q.toSet ∩ Metric.closedBall c δ).Nonempty →
        i0 - 1 ≤ q.i ∧ q.i ≤ i0 + 1 ∧ j0 - 1 ≤ q.j ∧ q.j ≤ j0 + 1 := by
    intro q hq
    rcases hq with ⟨x, hxq, hxball⟩
    have hdist : dist x c ≤ δ := Metric.mem_closedBall.mp hxball
    have hcoord0 : |x 0 - c 0| ≤ dist x c := DyadicCube.coord_abs_le_norm (x - c) 0
    have hcoord1 : |x 1 - c 1| ≤ dist x c := DyadicCube.coord_abs_le_norm (x - c) 1
    have h0 : |x 0 - c 0| ≤ δ := hcoord0.trans hdist
    have h1 : |x 1 - c 1| ≤ δ := hcoord1.trans hdist
    have hxq' := (q.mem_toSet_iff x).mp hxq
    have h_i1 : i0 - 1 ≤ q.i := by
      have h2 : c 0 - δ ≤ x 0 := by linarith [abs_le.mp h0]
      have h3 : x 0 < ((q.i : ℝ) + 1) * δ := hxq'.2.1
      have h4 : (i0 : ℝ) < (q.i : ℝ) + 2 := by
        have h5 : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le _
        nlinarith [hδ]
      have h6 : i0 < q.i + 2 := by exact_mod_cast h4
      linarith
    have h_i2 : q.i ≤ i0 + 1 := by
      have h2 : x 0 ≤ c 0 + δ := by linarith [abs_le.mp h0]
      have h3 : (q.i : ℝ) * δ ≤ x 0 := hxq'.1
      have h4 : (q.i : ℝ) < (i0 : ℝ) + 2 := by
        nlinarith [hδ, h_i02]
      have h5 : q.i < i0 + 2 := by exact_mod_cast h4
      linarith
    have h_j1 : j0 - 1 ≤ q.j := by
      have h2 : c 1 - δ ≤ x 1 := by linarith [abs_le.mp h1]
      have h3 : x 1 < ((q.j : ℝ) + 1) * δ := hxq'.2.2.2
      have h4 : (j0 : ℝ) < (q.j : ℝ) + 2 := by
        have h5 : (j0 : ℝ) ≤ c 1 / δ := Int.floor_le _
        nlinarith [hδ]
      have h6 : j0 < q.j + 2 := by exact_mod_cast h4
      linarith
    have h_j2 : q.j ≤ j0 + 1 := by
      have h2 : x 1 ≤ c 1 + δ := by linarith [abs_le.mp h1]
      have h3 : (q.j : ℝ) * δ ≤ x 1 := hxq'.2.2.1
      have h4 : (q.j : ℝ) < (j0 : ℝ) + 2 := by
        nlinarith [hδ, h_j02]
      have h5 : q.j < j0 + 2 := by exact_mod_cast h4
      linarith
    exact ⟨h_i1, h_i2, h_j1, h_j2⟩
  let Ix : Finset ℤ := Finset.Icc (i0 - 1) (i0 + 1)
  let Jy : Finset ℤ := Finset.Icc (j0 - 1) (j0 + 1)
  let Idx : Finset (ℤ × ℤ) := Ix ×ˢ Jy
  let f : ℤ × ℤ → DyadicCube n := fun p => ⟨p.1, p.2⟩
  let S : Finset (DyadicCube n) := Idx.image f
  have h_inj : Set.InjOn f Idx := by
    intro p1 _ p2 _ h
    have hi : p1.1 = p2.1 := by simpa [f] using congr_arg (fun q : DyadicCube n => q.i) h
    have hj : p1.2 = p2.2 := by simpa [f] using congr_arg (fun q : DyadicCube n => q.j) h
    exact Prod.ext hi hj
  have hIcc3 : ∀ (k : ℤ), (Finset.Icc (k - 1) (k + 1)).card = 3 := by
    intro k
    rw [Int.card_Icc]
    have h : ((k + 1 + 1 - (k - 1)) : ℤ) = 3 := by omega
    exact congr_arg (fun x : ℤ => x.toNat) h
  have hS_card : S.card = 9 := by
    rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have h1 : Ix.card = 3 := hIcc3 i0
    have h2 : Jy.card = 3 := hIcc3 j0
    rw [h1, h2] <;> norm_num
  let this : Finset (DyadicCube n) :=
    (D_nSet_finite n (A := Metric.closedBall c δ) Metric.isBounded_closedBall).toFinset
  have h_subset : this ⊆ S := by
    intro q hq
    have hq' : q ∈ D_nSet n (Metric.closedBall c δ) := by
      simpa [this, Set.Finite.mem_toFinset] using hq
    have h_b := h_bounds q hq'
    have h_i : q.i ∈ Ix := Finset.mem_Icc.mpr ⟨h_b.1, h_b.2.1⟩
    have h_j : q.j ∈ Jy := Finset.mem_Icc.mpr ⟨h_b.2.2.1, h_b.2.2.2⟩
    have h_pair : (q.i, q.j) ∈ Idx := Finset.mem_product.mpr ⟨h_i, h_j⟩
    have h_f : f (q.i, q.j) = q := by
      cases q <;> simp [f] <;> rfl
    exact Finset.mem_image.mpr ⟨(q.i, q.j), h_pair, h_f⟩
  have h_final : this.card ≤ S.card := Finset.card_le_card h_subset
  rw [hS_card] at h_final
  exact h_final

/-- externalCoveringNumber δ A ≤ dyadicCoveringNumber. -/
lemma dyadicCoveringNumber_le_external (n : ℕ) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal A ≤
      ↑(dyadicCoveringNumber n A hA) := by
  let δ := dyadicDelta n
  have hδ : 0 < δ := dyadicDelta_pos n
  have hδnn : (δ.toNNReal : ℝ) = δ := by
    simp [NNReal.coe_mk, hδ.le]
  let S : Finset (DyadicCube n) := D_nFinset n A hA
  let centers : Finset EuclideanPlane := S.image (fun q => q.center)
  have hcover : Metric.IsCover δ.toNNReal A (centers : Set EuclideanPlane) := by
    intro x hx
    have h1 : ∃ (q : DyadicCube n), x ∈ q.toSet := by
      have hcov : (⋃ (i : ℤ), ⋃ (j : ℤ), (⟨i, j⟩ : DyadicCube n).toSet) = Set.univ :=
        DyadicCube.cover n
      have h2 : x ∈ (⋃ (i : ℤ), ⋃ (j : ℤ), (⟨i, j⟩ : DyadicCube n).toSet) := by
        rw [hcov] <;> trivial
      have h3 : ∃ (i : ℤ), ∃ (j : ℤ), x ∈ (⟨i, j⟩ : DyadicCube n).toSet := by
        simpa [Set.mem_iUnion] using h2
      rcases h3 with ⟨i, j, hq⟩
      exact ⟨⟨i, j⟩, hq⟩
    rcases h1 with ⟨q, hq⟩
    have hqS : q ∈ S := by
      rw [D_nFinset_mem]
      exact ⟨x, hq, hx⟩
    have hcenter : q.center ∈ (centers : Set EuclideanPlane) := by
      exact Finset.mem_image.mpr ⟨q, hqS, rfl⟩
    have hdist : dist x q.center ≤ δ := DyadicCube.dist_center_le hq
    have hdist' : dist x q.center ≤ (δ.toNNReal : ℝ) := by
      rw [hδnn] <;> exact hdist
    have hedist : edist x q.center ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_coe.mpr hdist'
    exact ⟨q.center, hcenter, by simpa using hedist⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ (centers : Set EuclideanPlane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h2 : (centers : Set EuclideanPlane).encard = ↑centers.card := by simp
  have h3 : centers.card ≤ S.card := Finset.card_image_le
  rw [h2] at h1
  have h4 : (↑centers.card : ENat) ≤ ↑S.card := by exact_mod_cast h3
  exact h1.trans h4

/-- dyadicCoveringNumber ≤ 9 * externalCoveringNumber. -/
lemma externalCoveringNumber_le_dyadic (n : ℕ) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) :
    ↑(dyadicCoveringNumber n A hA) ≤
      9 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal A := by
  let δ := dyadicDelta n
  have hδ : 0 < δ := dyadicDelta_pos n
  have hδnn : (δ.toNNReal : ℝ) = δ := by
    simp [NNReal.coe_mk, hδ.le]
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
  · rw [h_top] <;> simp
  have hfin : Metric.externalCoveringNumber δ.toNNReal A < ⊤ :=
    lt_top_iff_ne_top.mpr h_top
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hfin with ⟨C, hC, h_eq⟩
  have hCfin : C.Finite := by
    have h : C.encard < ⊤ := h_eq.symm ▸ hfin
    exact Set.encard_lt_top_iff.mp h
  let Cfin : Finset EuclideanPlane := hCfin.toFinset
  have hCfin_coe : (Cfin : Set EuclideanPlane) = C := by
    ext z; simp [Cfin, Set.Finite.mem_toFinset]
  let Q (c : EuclideanPlane) : Finset (DyadicCube n) :=
    (D_nSet_finite n (A := Metric.closedBall c δ) Metric.isBounded_closedBall).toFinset
  have hQ9 : ∀ c ∈ Cfin, (Q c).card ≤ 9 := by
    intro c _
    exact ball_9_cubes n c
  have h_union : D_nFinset n A hA ⊆ Cfin.biUnion Q := by
    intro q hq
    have hq' : (q.toSet ∩ A).Nonempty := (D_nFinset_mem n).mp hq
    rcases hq' with ⟨y, hy_q, hy_A⟩
    rcases hC hy_A with ⟨c, hc, hpair⟩
    have hedist : edist y c ≤ ↑δ.toNNReal := by simpa using hpair
    have hcfin : c ∈ Cfin := by
      have h : c ∈ (Cfin : Set EuclideanPlane) := by
        rw [hCfin_coe] <;> exact hc
      exact_mod_cast h
    have hdist : dist y c ≤ δ := by
      rw [edist_dist] at hedist
      have h9 : dist y c ≤ (δ.toNNReal : ℝ) := ENNReal.ofReal_le_coe.mp hedist
      rw [hδnn] at h9
      exact h9
    have hqball : (q.toSet ∩ Metric.closedBall c δ).Nonempty := by
      exact ⟨y, hy_q, Metric.mem_closedBall.mpr hdist⟩
    have hqQ : q ∈ Q c := by
      simp only [Q, Set.Finite.mem_toFinset, D_nSet, Set.mem_setOf_eq]
      exact hqball
    exact Finset.mem_biUnion.mpr ⟨c, hcfin, hqQ⟩
  have h_card : (D_nFinset n A hA).card ≤ (Cfin.biUnion Q).card :=
    Finset.card_le_card h_union
  have h_biUnion : (Cfin.biUnion Q).card ≤ ∑ c ∈ Cfin, (Q c).card :=
    Finset.card_biUnion_le
  have h_sum : ∑ c ∈ Cfin, (Q c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
    apply Finset.sum_le_sum
    intro c hc
    exact hQ9 c hc
  have h_sum9 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
    simp [Finset.sum_const] <;> ring
  have h_final : (D_nFinset n A hA).card ≤ 9 * Cfin.card := by
    calc (D_nFinset n A hA).card
      ≤ (Cfin.biUnion Q).card := h_card
    _ ≤ ∑ c ∈ Cfin, (Q c).card := h_biUnion
    _ ≤ ∑ c ∈ Cfin, (9 : ℕ) := h_sum
    _ = 9 * Cfin.card := h_sum9
  have h_Ccard : C.encard = ↑Cfin.card := by
    rw [← hCfin_coe]
    simp
  have h5 : (↑(D_nFinset n A hA).card : ENat) ≤ ↑(9 * Cfin.card) := by
    exact_mod_cast h_final
  have h6 : (↑(9 * Cfin.card) : ENat) = 9 * C.encard := by
    simp [h_Ccard] <;> ring
  have h7 : (↑(D_nFinset n A hA).card : ENat) ≤ 9 * C.encard := by
    calc (↑(D_nFinset n A hA).card : ENat)
      ≤ ↑(9 * Cfin.card) := h5
    _ = 9 * C.encard := h6
  rw [h_eq] at h7
  simpa [dyadicCoveringNumber] using h7

/-- Full comparability: external ≤ dyadic ≤ 9 * external. -/
theorem dyadicCoveringNumber_comparable (n : ℕ) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal A ≤
      ↑(dyadicCoveringNumber n A hA) ∧
    ↑(dyadicCoveringNumber n A hA) ≤
      9 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal A :=
  ⟨dyadicCoveringNumber_le_external n hA, externalCoveringNumber_le_dyadic n hA⟩

/-! ### Connection with general dyadic covering number -/

/-- `toSet` is injective: distinct dyadic cubes have distinct sets. -/
lemma DyadicCube.toSet_injective (n : ℕ) :
    Function.Injective (fun (q : DyadicCube n) => q.toSet) := by
  intro q1 q2 h
  set δ := dyadicDelta n with hδ_def
  have hδ : 0 < δ := dyadicDelta_pos n
  have h1a : q1.lower ∈ q1.toSet := q1.lower_mem
  have h1 : q1.lower ∈ q2.toSet := by
    have h_eq : q1.toSet = q2.toSet := h
    simpa [h_eq] using h1a
  have h2 := (q2.mem_toSet_iff q1.lower).mp h1
  have hside1 : q1.side = δ := by rfl
  have hlo0 : q1.lower 0 = (q1.i : ℝ) * δ := by
    have h : q1.lower 0 = (q1.i : ℝ) * q1.side := by
      simp [DyadicCube.lower, DyadicCube.mkPoint_apply0]
    rw [h, hside1]
  have hlo1 : q1.lower 1 = (q1.j : ℝ) * δ := by
    have h : q1.lower 1 = (q1.j : ℝ) * q1.side := by
      simp [DyadicCube.lower, DyadicCube.mkPoint_apply1]
    rw [h, hside1]
  have h_i1 : (q2.i : ℝ) ≤ (q1.i : ℝ) := by
    have h3 : (q2.i : ℝ) * δ ≤ q1.lower 0 := h2.1
    rw [hlo0] at h3
    nlinarith
  have h_i2 : (q1.i : ℝ) < (q2.i : ℝ) + 1 := by
    have h4 : q1.lower 0 < ((q2.i : ℝ) + 1) * δ := h2.2.1
    rw [hlo0] at h4
    nlinarith
  have h_i1' : q2.i ≤ q1.i := by exact_mod_cast h_i1
  have h_i2' : q1.i < q2.i + 1 := by exact_mod_cast h_i2
  have h_i : q1.i = q2.i := by omega
  have h_j1 : (q2.j : ℝ) ≤ (q1.j : ℝ) := by
    have h3 : (q2.j : ℝ) * δ ≤ q1.lower 1 := h2.2.2.1
    rw [hlo1] at h3
    nlinarith
  have h_j2 : (q1.j : ℝ) < (q2.j : ℝ) + 1 := by
    have h4 : q1.lower 1 < ((q2.j : ℝ) + 1) * δ := h2.2.2.2
    rw [hlo1] at h4
    nlinarith
  have h_j1' : q2.j ≤ q1.j := by exact_mod_cast h_j1
  have h_j2' : q1.j < q2.j + 1 := by exact_mod_cast h_j2
  have h_j : q1.j = q2.j := by omega
  cases q1 <;> cases q2 <;> simp [h_i, h_j] <;> tauto

/-- A general dyadic cube equals the `toSet` of a `DyadicCube n`. -/
lemma general_cube_eq_toSet (n : ℕ) (k : Fin 2 → ℤ) :
    dyadicCube (dyadicDelta n) k = (⟨k 0, k 1⟩ : DyadicCube n).toSet := by
  ext x
  let δ := dyadicDelta n
  simp only [dyadicCube, DyadicCube.toSet, Set.mem_setOf_eq,
    Fin.forall_fin_succ, Set.mem_Ico]
  have h_comm : ∀ (z : ℤ), δ * (z : ℝ) = (z : ℝ) * δ := by intro z; ring
  have h_comm_add1 : ∀ (z : ℤ), δ * ((z : ℝ) + 1) = ((z : ℝ) + 1) * δ := by intro z; ring
  constructor <;> intro h <;> simp [h_comm, h_comm_add1] at h ⊢ <;> aesop

/-- The general `dyadicCubesMeeting` equals the image of `D_nSet` under `toSet`. -/
lemma dyadicCubesMeeting_eq_image (n : ℕ) (A : Set EuclideanPlane) :
    dyadicCubesMeeting (dyadicDelta n) A =
      (fun (q : DyadicCube n) => q.toSet) '' D_nSet n A := by
  ext p
  simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQ, hnonempty⟩
    rcases hQ with ⟨k, rfl⟩
    let q : DyadicCube n := ⟨k 0, k 1⟩
    have h_eq : dyadicCube (dyadicDelta n) k = q.toSet := general_cube_eq_toSet n k
    refine ⟨q, ?_, h_eq.symm⟩
    simp only [D_nSet, Set.mem_setOf_eq]
    rw [←h_eq]
    exact hnonempty
  · rintro ⟨q, hq, rfl⟩
    let k : Fin 2 → ℤ := fun i => if i = 0 then q.i else q.j
    have hQ : q.toSet ∈ dyadicCubes 2 (dyadicDelta n) := by
      refine ⟨k, ?_⟩
      exact (general_cube_eq_toSet n k).symm
    exact ⟨hQ, hq⟩

/-- The general `dyadicCoveringNumber` equals the specialized one. -/
lemma dyadicCoveringNumber_eq_general (n : ℕ) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) :
    (dyadicCubesMeeting (dyadicDelta n) A).encard = ↑(dyadicCoveringNumber n A hA) := by
  have h1 := dyadicCubesMeeting_eq_image n A
  rw [h1]
  have h2 : Set.InjOn (fun (q : DyadicCube n) => q.toSet) (D_nSet n A) :=
    fun x _ y _ h => DyadicCube.toSet_injective n h
  have h3 : ((fun (q : DyadicCube n) => q.toSet) '' D_nSet n A).encard = (D_nSet n A).encard :=
    h2.encard_image
  rw [h3]
  have h4 : (D_nSet n A).encard = ↑(D_nFinset n A hA).card := by
    let hfin := D_nSet_finite n hA
    have h5 : (D_nSet n A).encard = ↑hfin.toFinset.card := by
      exact Set.Finite.encard_eq_coe_toFinset_card hfin
    simpa [D_nFinset] using h5
  rw [h4]
  <;> rfl

end DiscretisedFurstenbergEstimate.DyadicCubes
