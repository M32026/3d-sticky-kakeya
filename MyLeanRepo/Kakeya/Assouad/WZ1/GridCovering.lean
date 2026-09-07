import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Grid covering helpers for WZ1

Reusable coordinate-grid covering lemmas extracted from the oriented
finite-cap refinement.  A finite grid of cubes covers a ball in `Point3`,
with explicit diameter and measurability bounds.
-/

namespace Kakeya.Assouad

open MeasureTheory Set Finset

lemma find_grid_index (a step : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (z : ℝ) (hz1 : a ≤ z) (hz2 : z ≤ a + N * step) :
    ∃ k : Fin N,
      a + (k : ℝ) * step ≤ z ∧
        z ≤ a + ((k : ℕ) + 1) * step := by
  by_cases hstep : step = 0
  · refine ⟨⟨0, by omega⟩, ?_⟩
    have hz : z = a := by
      rw [hstep] at hz2
      linarith
    rw [hz, hstep] <;> norm_num
  · have hstep_nonneg : 0 ≤ step := by
      by_contra h
      have h' : step < 0 := by linarith
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have : a + N * step < a := by nlinarith
      linarith
    have hstep_pos : 0 < step :=
      lt_of_le_of_ne hstep_nonneg (Ne.symm hstep)
    set u : ℝ := (z - a) / step with hu_def
    have hu0 : 0 ≤ u := by
      have h : 0 ≤ z - a := by linarith
      exact div_nonneg h hstep_nonneg
    have huN : u ≤ (N : ℝ) := by
      have h : z - a ≤ N * step := by linarith
      have h2 : (z - a) / step ≤ (N * step) / step := by gcongr
      have h3 : (N * step) / step = (N : ℝ) := by
        field_simp [hstep] <;> ring
      rw [h3] at h2
      exact h2
    set m : ℕ := Nat.floor u with hm_def
    have hm1 : (m : ℝ) ≤ u := Nat.floor_le hu0
    have hm2 : u < (m : ℝ) + 1 := Nat.lt_floor_add_one u
    by_cases hmN : m < N
    · let k : Fin N := ⟨m, hmN⟩
      refine ⟨k, ?_⟩
      have h4 : a + (m : ℝ) * step ≤ z := by
        have h5 : (m : ℝ) * step ≤ u * step := by gcongr
        have h6 : u * step = z - a := by
          simp [hu_def]
          field_simp [hstep] <;> ring
        linarith
      have h5 : z ≤ a + ((m : ℕ) + 1) * step := by
        have h6 : u * step ≤ ((m : ℕ) + 1) * step := by gcongr
        have h7 : u * step = z - a := by
          simp [hu_def]
          field_simp [hstep] <;> ring
        linarith
      exact ⟨h4, h5⟩
    · have hge : N ≤ m := by omega
      have h10 : (N : ℝ) ≤ u := by
        have h9 : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hge
        linarith
      have h11 : u = (N : ℝ) := by linarith
      let k : Fin N := ⟨N - 1, by omega⟩
      refine ⟨k, ?_⟩
      have h12 : a + ((N - 1 : ℕ) : ℝ) * step ≤ z := by
        have h13 : u * step = z - a := by
          simp [hu_def]
          field_simp [hstep] <;> ring
        have h14 : ((N - 1 : ℕ) : ℝ) * step ≤ u * step := by
          rw [h11]
          simp [hstep_pos] <;> ring_nf <;> nlinarith
        linarith
      have h15 : z ≤ a + (((N - 1 : ℕ) : ℝ) + 1) * step := by
        have h16 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
          have h17 : N ≥ 1 := hN
          simp [h17] <;> omega
        rw [h16]
        have h18 : z - a ≤ (N : ℝ) * step := by linarith
        linarith
      simpa [k] using ⟨h12, h15⟩

lemma coord_bound (v : Point3) (j : Fin 3) :
    |v j| ≤ ‖v‖ := by
  have h2 : ‖v‖ ^ 2 = ∑ i : Fin 3, |v i| ^ 2 := by
    have h3 : ‖v‖ = Real.sqrt (∑ i : Fin 3, |v i| ^ 2) :=
      PiLp.norm_eq_of_L2 v
    rw [h3]
    have h4 : 0 ≤ ∑ i : Fin 3, |v i| ^ 2 := by positivity
    rw [Real.sq_sqrt h4] <;> rfl
  have h5 : |v j| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h2]
    have h6 :
        ∀ i ∈ (Finset.univ : Finset (Fin 3)),
          0 ≤ |v i| ^ 2 := by
      intro i _
      positivity
    exact Finset.single_le_sum h6 (Finset.mem_univ j)
  have h7 : 0 ≤ |v j| := by positivity
  have h8 : 0 ≤ ‖v‖ := by positivity
  nlinarith

def gridCube (center : Point3) (radius step : ℝ) (N : ℕ)
    (k : Fin 3 → Fin N) : Set Point3 :=
  {x |
    ∀ j : Fin 3,
      x j ∈
        Set.Icc
          (center j - radius + (k j : ℝ) * step)
          (center j - radius + ((k j : ℕ) + 1) * step)}

lemma gridCube_measurable {center radius step N k} :
    MeasurableSet (gridCube center radius step N k) := by
  have hproj :
      ∀ j : Fin 3, Measurable (fun p : Point3 => p j) := by
    intro j
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable
  have h1 :
      gridCube center radius step N k =
        ⋂ j : Fin 3,
          (fun p : Point3 => p j) ⁻¹'
            Set.Icc
              (center j - radius + (k j : ℝ) * step)
              (center j - radius + ((k j : ℕ) + 1) * step) := by
    ext x
    simp [gridCube, Set.mem_iInter] <;> rfl
  rw [h1]
  apply MeasurableSet.iInter
  intro j
  exact hproj j measurableSet_Icc

lemma gridCube_diameter {center radius step N k x y}
    (hstep : 0 ≤ step)
    (hx : x ∈ gridCube center radius step N k)
    (hy : y ∈ gridCube center radius step N k) :
    dist x y ≤ Real.sqrt 3 * step := by
  have h4 : ∀ j, |x j - y j| ≤ step := by
    intro j
    have h5 :
        center j - radius + (k j : ℝ) * step ≤ x j :=
      (hx j).1
    have h6 :
        x j ≤ center j - radius + ((k j : ℕ) + 1) * step :=
      (hx j).2
    have h7 :
        center j - radius + (k j : ℝ) * step ≤ y j :=
      (hy j).1
    have h8 :
        y j ≤ center j - radius + ((k j : ℕ) + 1) * step :=
      (hy j).2
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have h5 :
      ∑ j : Fin 3, (x j - y j) ^ 2 ≤
        ∑ _j : Fin 3, step ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have h6 : |x j - y j| ≤ step := h4 j
    calc
      (x j - y j) ^ 2 = |x j - y j| ^ 2 := by rw [sq_abs]
      _ ≤ step ^ 2 := by gcongr
  have h5' :
      ∑ j : Fin 3, (x j - y j) ^ 2 ≤ 3 * step ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin 3, step ^ 2 := h5
      _ = 3 * step ^ 2 := by
        simp [Finset.sum_const] <;> ring
  have h6 :
      ‖x - y‖ ^ 2 = ∑ j : Fin 3, (x j - y j) ^ 2 := by
    have h7 :
        ‖x - y‖ =
          Real.sqrt (∑ j : Fin 3, |(x - y) j| ^ 2) :=
      PiLp.norm_eq_of_L2 (x - y)
    rw [h7]
    have h8 : 0 ≤ ∑ j : Fin 3, |(x - y) j| ^ 2 := by positivity
    rw [Real.sq_sqrt h8]
    apply Finset.sum_congr rfl
    intro j _
    have h9 : (x - y) j = x j - y j := by rfl
    rw [h9, sq_abs]
  have h10 : ‖x - y‖ ^ 2 ≤ (Real.sqrt 3 * step) ^ 2 := by
    rw [h6]
    have h11 : (Real.sqrt 3 * step) ^ 2 = 3 * step ^ 2 := by
      have h12 : (Real.sqrt 3) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      calc
        (Real.sqrt 3 * step) ^ 2 =
            (Real.sqrt 3) ^ 2 * step ^ 2 := by ring
        _ = 3 * step ^ 2 := by rw [h12]
    rw [h11]
    exact h5'
  have h13 : 0 ≤ ‖x - y‖ := by positivity
  have h14 : 0 ≤ Real.sqrt 3 * step := by positivity
  have h15 : ‖x - y‖ ≤ Real.sqrt 3 * step := by nlinarith
  rw [dist_eq_norm]
  exact h15

lemma grid_covering_cover
    (center : Point3) (radius scale : ℝ)
    (hradius : 0 ≤ radius)
    (N : ℕ) (hN : 1 ≤ N)
    (hscale : 0 < scale)
    (hdiam : Real.sqrt 3 * (2 * radius / N) ≤ scale) :
    ∃ C : (Fin 3 → Fin N) → Set Point3,
      (∀ k, MeasurableSet (C k)) ∧
      (∀ x, dist x center ≤ radius → ∃ k, x ∈ C k) ∧
      ∀ k x y, x ∈ C k → y ∈ C k → dist x y ≤ scale := by
  classical
  let step : ℝ := 2 * radius / N
  have hstep0 : 0 ≤ step := by positivity
  let C : (Fin 3 → Fin N) → Set Point3 :=
    gridCube center radius step N
  have hcover1 :
      ∀ x : Point3,
        (∀ j, |x j - center j| ≤ radius) →
          ∃ k : Fin 3 → Fin N, x ∈ C k := by
    intro x hx
    have h_all :
        ∀ j : Fin 3,
          ∃ k : Fin N,
            center j - radius + (k : ℝ) * step ≤ x j ∧
            x j ≤ center j - radius + ((k : ℕ) + 1) * step := by
      intro j
      have h1 : center j - radius ≤ x j := by
        linarith [abs_le.mp (hx j)]
      have h2 : x j ≤ center j + radius := by
        linarith [abs_le.mp (hx j)]
      have h3 :
          x j ≤ (center j - radius) + N * step := by
        have h4 :
            center j + radius =
              (center j - radius) + N * step := by
          simp [step] <;> field_simp <;> ring
        rw [h4] at h2
        exact h2
      exact
        find_grid_index
          (center j - radius) step N hN (x j) h1 h3
    choose k hk using h_all
    exact ⟨k, fun j => ⟨(hk j).1, (hk j).2⟩⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro k
    exact gridCube_measurable
  · intro x hx
    have hcoord : ∀ j, |x j - center j| ≤ radius := by
      intro j
      have h1 :
          |(x - center) j| ≤ ‖x - center‖ :=
        coord_bound (x - center) j
      have hdist : ‖x - center‖ = dist x center := by
        rw [dist_eq_norm]
      rw [hdist] at h1
      exact h1.trans hx
    exact hcover1 x hcoord
  · intro k x y hxk hyk
    have h :
        dist x y ≤ Real.sqrt 3 * step :=
      gridCube_diameter hstep0 hxk hyk
    have h2 : Real.sqrt 3 * step ≤ scale := by
      simpa [step] using hdiam
    linarith

lemma exists_ge_average
    {α : Type*} [Fintype α] [Nonempty α] (f : α → ENNReal) :
    ∃ a : α,
      (Fintype.card α : ENNReal) * f a ≥ ∑ x : α, f x := by
  classical
  obtain ⟨a, _, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset α) f (by simp)
  have hsum :
      ∑ x : α, f x ≤
        (Fintype.card α : ENNReal) * f a := by
    calc
      ∑ x : α, f x ≤ ∑ _x : α, f a := by
        exact Finset.sum_le_sum
          (fun i _ => hmax i (Finset.mem_univ i))
      _ = (Fintype.card α : ENNReal) * f a := by
        simp [Finset.sum_const] <;> ring
  exact ⟨a, hsum⟩

end Kakeya.Assouad
