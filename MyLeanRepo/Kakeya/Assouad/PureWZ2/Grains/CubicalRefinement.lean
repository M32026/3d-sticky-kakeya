import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import Mathlib.Tactic

/-!
# Cubical plane map refinement (WZ1 Lemma 13 adaptation)

Refine a coarse plane map (constant on `rho`-grid cells) to a fine plane map
(constant on `delta`-grid cells) using the direction alignment from the paper
cover relation.

## Key idea

If `rho = K * delta` for a positive integer `K`, then every `delta`-grid cell
is contained in a `rho`-grid cell. A map constant on `rho`-cells is therefore
automatically constant on `delta`-cells.

The incidence bound transfers from coarse to fine via direction alignment:
  `|inner(d_fine, n)| ≤ |inner(d_coarse, n)| + ‖d_fine - d_coarse‖`
  `≤ I + rho/2`

where the second term comes from `paper_cover_direction_alignment`.

## Grid alignment

`wz1PaperGridIndex scale p = floor(p / scale)` componentwise.
If `rho = K * delta`, then:
  `wz1PaperGridIndex rho p = floor(wz1PaperGridIndex delta p / K)`
so same delta-index implies same rho-index.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- If `⌊x⌋ = ⌊y⌋`, then `⌊x / K⌋ = ⌊y / K⌋` for positive integer `K`.

The interval `[⌊x⌋/K, (⌊x⌋+1)/K)` has length `1/K ≤ 1` and contains no integer
in its interior, so `floor` is constant on it. -/
lemma floor_div_nat_congr {x y : ℝ} {K : ℕ} (hK_pos : 0 < K)
    (h : ⌊x⌋ = ⌊y⌋) : ⌊x / (K : ℝ)⌋ = ⌊y / (K : ℝ)⌋ := by
  set n : ℤ := ⌊x⌋ with hn
  have hnx : (n : ℝ) ≤ x := Int.floor_le x
  have hxp : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have h_eq : n = ⌊y⌋ := hn.trans h
  have hny : (n : ℝ) ≤ y := by
    rw [h_eq]
    exact Int.floor_le y
  have hyp : y < (n : ℝ) + 1 := by
    rw [h_eq]
    exact Int.lt_floor_add_one y
  set m : ℤ := ⌊x / (K : ℝ)⌋ with hm
  have h1 : (m : ℝ) ≤ x / (K : ℝ) := Int.floor_le (x / (K : ℝ))
  have h2 : x / (K : ℝ) < (m : ℝ) + 1 := Int.lt_floor_add_one (x / (K : ℝ))
  have hmk_le_n : m * K ≤ n := by
    have h3 : (m : ℝ) * (K : ℝ) ≤ x := by
      have h31 : (m : ℝ) ≤ x / (K : ℝ) := h1
      calc (m : ℝ) * (K : ℝ)
          ≤ (x / (K : ℝ)) * (K : ℝ) := by gcongr
        _ = x := by field_simp [hK_pos.ne'] <;> ring
    have h4 : (m : ℝ) * (K : ℝ) < (n : ℝ) + 1 := by
      calc (m : ℝ) * (K : ℝ) ≤ x := h3
        _ < (n : ℝ) + 1 := hxp
    have h5 : m * K < n + 1 := by exact_mod_cast h4
    omega
  have h_n1_le_mk1 : n + 1 ≤ (m + 1) * K := by
    have h3 : x < ((m : ℝ) + 1) * (K : ℝ) := by
      calc x
          = (x / (K : ℝ)) * (K : ℝ) := by field_simp [hK_pos.ne'] <;> ring
        _ < ((m : ℝ) + 1) * (K : ℝ) := by gcongr
    have h4 : (n : ℝ) < ((m : ℝ) + 1) * (K : ℝ) := by
      exact lt_of_le_of_lt hnx h3
    have h5 : n < (m + 1) * K := by exact_mod_cast h4
    omega
  have h_m_le_nK : (m : ℝ) ≤ (n : ℝ) / (K : ℝ) := by
    have h6 : (m : ℝ) * (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmk_le_n
    calc (m : ℝ)
        = (m : ℝ) * (K : ℝ) / (K : ℝ) := by field_simp [hK_pos.ne'] <;> ring
      _ ≤ (n : ℝ) / (K : ℝ) := by gcongr
  have h_n1K_le_m1 : ((n : ℝ) + 1) / (K : ℝ) ≤ (m : ℝ) + 1 := by
    have h7 : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) * (K : ℝ) := by exact_mod_cast h_n1_le_mk1
    calc ((n : ℝ) + 1) / (K : ℝ)
        ≤ (((m : ℝ) + 1) * (K : ℝ)) / (K : ℝ) := by gcongr
      _ = (m : ℝ) + 1 := by field_simp [hK_pos.ne'] <;> ring
  have h_y1 : (m : ℝ) ≤ y / (K : ℝ) := by
    have h8 : (n : ℝ) / (K : ℝ) ≤ y / (K : ℝ) := by gcongr
    linarith
  have h_y2 : y / (K : ℝ) < (m : ℝ) + 1 := by
    have h9 : y / (K : ℝ) < ((n : ℝ) + 1) / (K : ℝ) := by gcongr
    linarith
  have h10 : ⌊y / (K : ℝ)⌋ = m := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast h_y1, by exact_mod_cast h_y2⟩
  rw [h10] <;> rfl

/-- Same `delta`-grid index implies same `rho`-grid index when `rho = K * delta`. -/
lemma wz1PaperGridIndex_fine_to_coarse
    {delta rho : ℝ} (K : ℕ) (hK_pos : 0 < K)
    (hrho_eq : rho = (K : ℝ) * delta)
    {p q : Point3}
    (h : wz1PaperGridIndex delta p = wz1PaperGridIndex delta q) :
    wz1PaperGridIndex rho p = wz1PaperGridIndex rho q := by
  have h1 : (wz1PaperGridIndex delta p).1 = (wz1PaperGridIndex delta q).1 := by rw [h]
  have h2 : (wz1PaperGridIndex delta p).2.1 = (wz1PaperGridIndex delta q).2.1 := by rw [h]
  have h3 : (wz1PaperGridIndex delta p).2.2 = (wz1PaperGridIndex delta q).2.2 := by rw [h]
  have hdiv : ∀ (x : ℝ), x / ((K : ℝ) * delta) = (x / delta) / (K : ℝ) := by
    intro x
    field_simp [hK_pos.ne'] <;> ring
  have h1' : ⌊(p 0) / rho⌋ = ⌊(q 0) / rho⌋ := by
    rw [hrho_eq]
    rw [hdiv (p 0), hdiv (q 0)]
    exact floor_div_nat_congr hK_pos h1
  have h2' : ⌊(p 1) / rho⌋ = ⌊(q 1) / rho⌋ := by
    rw [hrho_eq]
    rw [hdiv (p 1), hdiv (q 1)]
    exact floor_div_nat_congr hK_pos h2
  have h3' : ⌊(p 2) / rho⌋ = ⌊(q 2) / rho⌋ := by
    rw [hrho_eq]
    rw [hdiv (p 2), hdiv (q 2)]
    exact floor_div_nat_congr hK_pos h3
  simp only [wz1PaperGridIndex, gridIndex]
  exact Prod.ext h1' (Prod.ext h2' h3')

/-- Refine a coarse plane map to a fine-scale cubical plane map.

Given a coarse plane map constant on `rho`-cells with incidence `I`, and a
paper cover from `delta`-tubes to `rho`-tubes with direction alignment, produce
a fine plane map constant on `delta`-cells with incidence `I + rho/2`.

The fine plane map is literally the same function as the coarse plane map;
the theorem packages the transfer of properties from coarse to fine.
-/
theorem pureWz2_cubical_refinement
    {delta rho I : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (cover : PureWZ2Section6Cover fine coarse)
    (point_compat :
      ∀ (source : Fin fine.card) (parent : Fin coarse.card),
        WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
          ∀ (point : Point3),
            point ∈ fineShading.carrier source →
              point ∈ coarseShading.carrier parent)
    (coarsePlaneMap : Point3 → Point3)
    (hcoarse_const :
      ∀ (p q : Point3),
        wz1PaperGridIndex rho p = wz1PaperGridIndex rho q →
          coarsePlaneMap p = coarsePlaneMap q)
    (hcoarse_unit :
      ∀ (p : Point3), p ∈ coarseShading.union → ‖coarsePlaneMap p‖ = 1)
    (hcoarse_inc :
      ∀ (j : Fin coarse.card) (p : Point3),
        p ∈ coarseShading.carrier j →
          |inner ℝ (wz1PaperDirection (coarse.tube j)) (coarsePlaneMap p)| ≤ I)
    (K : ℕ) (hK_pos : 0 < K)
    (hrho_eq : rho = (K : ℝ) * delta) :
    ∃ (finePlaneMap : Point3 → Point3),
      (∀ (p q : Point3),
        wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
          finePlaneMap p = finePlaneMap q) ∧
      (∀ (p : Point3), p ∈ fineShading.union → ‖finePlaneMap p‖ = 1) ∧
      (∀ (i : Fin fine.card) (p : Point3),
        p ∈ fineShading.carrier i →
          |inner ℝ (wz1PaperDirection (fine.tube i)) (finePlaneMap p)| ≤ I + rho / 2) := by
  classical
  let finePlaneMap : Point3 → Point3 := coarsePlaneMap
  have hfine_const : ∀ (p q : Point3),
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        finePlaneMap p = finePlaneMap q := by
    intro p q h
    have h_rho : wz1PaperGridIndex rho p = wz1PaperGridIndex rho q :=
      wz1PaperGridIndex_fine_to_coarse K hK_pos hrho_eq h
    exact hcoarse_const p q h_rho
  have hfine_unit : ∀ (p : Point3), p ∈ fineShading.union → ‖finePlaneMap p‖ = 1 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    have hcover : ∃ (j : Fin coarse.card),
        WZ1PaperTubeCovers (fine.tube i) (coarse.tube j) :=
      cover.covers i
    rcases hcover with ⟨j, hcov⟩
    have h_p_in_coarse : p ∈ coarseShading.carrier j :=
      point_compat i j hcov p hi
    have h_p_in_union : p ∈ coarseShading.union := ⟨j, h_p_in_coarse⟩
    exact hcoarse_unit p h_p_in_union
  have hfine_inc : ∀ (i : Fin fine.card) (p : Point3),
      p ∈ fineShading.carrier i →
        |inner ℝ (wz1PaperDirection (fine.tube i)) (finePlaneMap p)| ≤ I + rho / 2 := by
    intro i p hp
    have hcover : ∃ (j : Fin coarse.card),
        WZ1PaperTubeCovers (fine.tube i) (coarse.tube j) :=
      cover.covers i
    rcases hcover with ⟨j, hcov⟩
    have h_p_in_coarse : p ∈ coarseShading.carrier j :=
      point_compat i j hcov p hp
    have h_p_in_union : p ∈ coarseShading.union := ⟨j, h_p_in_coarse⟩
    have h_unit : ‖coarsePlaneMap p‖ = 1 := hcoarse_unit p h_p_in_union
    have h_coarse_inc :
        |inner ℝ (wz1PaperDirection (coarse.tube j)) (coarsePlaneMap p)| ≤ I :=
      hcoarse_inc j p h_p_in_coarse
    have h_align :
        ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ ≤ rho / 2 :=
      paper_cover_direction_alignment hcov
    have h_inner_diff :
        |inner ℝ (wz1PaperDirection (fine.tube i)) (coarsePlaneMap p) -
           inner ℝ (wz1PaperDirection (coarse.tube j)) (coarsePlaneMap p)| ≤
        ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ := by
      have h : inner ℝ (wz1PaperDirection (fine.tube i)) (coarsePlaneMap p) -
                   inner ℝ (wz1PaperDirection (coarse.tube j)) (coarsePlaneMap p) =
                 inner ℝ (wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j))
                   (coarsePlaneMap p) := by
        simp [inner_sub_left]
        <;> abel
      rw [h]
      have h2 : |inner ℝ (wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j))
                     (coarsePlaneMap p)| ≤
                 ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ *
                 ‖coarsePlaneMap p‖ :=
        abs_real_inner_le_norm _ _
      rw [h_unit] at h2
      simpa using h2
    set a : ℝ := inner ℝ (wz1PaperDirection (fine.tube i)) (coarsePlaneMap p) with ha
    set b : ℝ := inner ℝ (wz1PaperDirection (coarse.tube j)) (coarsePlaneMap p) with hb
    have h_reverse_triangle : |a| ≤ |b| + |a - b| := by
      have h : |a| = |b + (a - b)| := by ring_nf
      rw [h]
      have h2 : |b + (a - b)| ≤ |b| + |a - b| := abs_add_le b (a - b)
      exact h2
    have h_main : |a| ≤ |b| + ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ := by
      calc
        |a| ≤ |b| + |a - b| := h_reverse_triangle
        _ ≤ |b| + ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ := by
          have h : |a - b| ≤ ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ := h_inner_diff
          linarith
    have h_goal : |b| + ‖wz1PaperDirection (fine.tube i) - wz1PaperDirection (coarse.tube j)‖ ≤ I + rho / 2 := by
      exact add_le_add h_coarse_inc h_align
    exact h_main.trans h_goal
  exact ⟨finePlaneMap, hfine_const, hfine_unit, hfine_inc⟩

end Kakeya.Assouad

end
