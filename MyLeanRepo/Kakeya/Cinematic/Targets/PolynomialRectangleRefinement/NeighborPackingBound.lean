import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking

/-!
# Per-ball neighbor packing bound

Extracts the inner neighbor-bound argument from `rectangle_refinement_part2`.

Given a central rectangle `S_j` and a family of pairwise-incomparable
neighbor rectangles that are all `comparison`-comparable to `S_j`, all
within distance `3*t` of a common center, this lemma bounds the number
of neighbors by a polynomial in `comparison`.

## Proof route

1. From `hComp_prop`, interval hulls are within `sqrt(comparison * delta / t)`
   and function values are within `C₁' * comparison^3 * delta`.
2. Build a containing interval `J` of length ≤ `2 * sqrt comparison * sqrt(delta/t)`.
3. Show all neighbor carriers lie in `verticalNeighborhoodOn S_j.function (lambda * delta) J`
   where `lambda := C₁' * comparison^3 + 1`.
4. Apply `generalized_packing_bound`.
5. Conclude `neighbors.card ≤ 42 * lambda^2 * (2 * Real.sqrt comparison)`.

## Whiteprint node

`polynomial-rectangle-refinement/neighbor-packing-bound`
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

/-- Per-ball neighbor packing bound.

Given a central rectangle `S_j` and a pairwise-100-incomparable family of
neighbor rectangles that are all `comparison`-comparable to `S_j`, bound
the neighbor count polynomially in `comparison`. -/
lemma neighbor_packing_bound
    {K : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function}
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t comparison : ℝ}
    (hdelta : 0 < delta) (hdt : delta ≤ t)
    (hcomparison : 100 ≤ comparison)
    {C₁' : ℝ} (hC₁'_one : 1 ≤ C₁')
    (hComp_prop :
      ∀ (lambda : ℝ), 1 ≤ lambda →
        ∀ (R S : CurvilinearRectangle delta t),
          R.function ∈ family → S.function ∈ family →
          R.IsOverCentralQuarterOf I → S.IsOverCentralQuarterOf I →
          R.AreLambdaComparable S family lambda →
          max R.interval.right S.interval.right - min R.interval.left S.interval.left ≤
            Real.sqrt (lambda * delta / t) ∧
          ∀ x ∈ R.intervalHullCarrier S,
            |R.function x - S.function x| ≤ C₁' * Real.rpow lambda 3 * delta)
    {S_j : CurvilinearRectangle delta t}
    (hSj_family : S_j.function ∈ family)
    (hSj_over : S_j.IsOverCentralQuarterOf I)
    {center : C2Function}
    {neighbors : RectangleFamily delta t}
    (h_neighbors_centers : neighbors.CentersIn family)
    (h_neighbors_over : neighbors.IsOverCentralQuarterOf I)
    (h_neighbors_incomp : neighbors.IsPairwiseIncomparable family 100)
    (h_neighbors_dist : ∀ i, c2Distance center (neighbors.rectangle i).function ≤ 3 * t)
    (h_neighbors_comparable :
      ∀ i, (neighbors.rectangle i).AreLambdaComparable S_j family comparison) :
    (neighbors.card : ℝ) ≤
      42 * (C₁' * comparison^3 + 1)^2 * (2 * Real.sqrt comparison) := by
  classical
  let B : ℝ := C₁' * comparison^3
  have hB_pos : 0 < B := by positivity
  let lambda : ℝ := B + 1
  have hlambda_100 : 100 ≤ lambda := by
    have h1 : 0 < C₁' := by linarith
    have h2 : comparison^3 ≥ 100^3 := by gcongr
    nlinarith
  let L : ℝ := Real.sqrt (delta / t)
  have hL_pos : 0 < L := Real.sqrt_pos.mpr (div_pos hdelta (by linarith))
  let d : ℝ := (Real.sqrt comparison - 1) * L
  have hd_nonneg : 0 ≤ d := by
    have h1 : 1 ≤ Real.sqrt comparison := by
      have h2 : (1 : ℝ)^2 ≤ comparison := by norm_num; linarith
      exact Real.le_sqrt_of_sq_le h2
    have h3 : 0 ≤ Real.sqrt comparison - 1 := by linarith
    positivity
  -- Hull bounds
  have h_hull_left : ∀ i : Fin neighbors.card,
      S_j.interval.left - d ≤ (neighbors.rectangle i).interval.left := by
    intro i
    have hcomp := h_neighbors_comparable i
    have h_main := (hComp_prop comparison (by linarith)
        (neighbors.rectangle i) S_j
        (h_neighbors_centers i) hSj_family
        (h_neighbors_over i) hSj_over hcomp).1
    have h2 : Real.sqrt (comparison * delta / t) = Real.sqrt comparison * L := by
      rw [show comparison * delta / t = comparison * (delta / t) by ring]
      rw [Real.sqrt_mul (by linarith)]
    rw [h2] at h_main
    have hSlen : S_j.interval.right - S_j.interval.left = L := by
      simpa [ParameterInterval.length] using S_j.interval_length
    by_cases h : (neighbors.rectangle i).interval.left ≤ S_j.interval.left
    · have h3 : min (neighbors.rectangle i).interval.left S_j.interval.left =
          (neighbors.rectangle i).interval.left := by
        rw [min_eq_left]; exact h
      rw [h3] at h_main
      have h4 : max (neighbors.rectangle i).interval.right S_j.interval.right ≥ S_j.interval.right :=
        le_max_right _ _
      linarith
    · have h3 : S_j.interval.left < (neighbors.rectangle i).interval.left := by linarith
      linarith
  have h_hull_right : ∀ i : Fin neighbors.card,
      (neighbors.rectangle i).interval.right ≤ S_j.interval.right + d := by
    intro i
    have hcomp := h_neighbors_comparable i
    have h_main := (hComp_prop comparison (by linarith)
        (neighbors.rectangle i) S_j
        (h_neighbors_centers i) hSj_family
        (h_neighbors_over i) hSj_over hcomp).1
    have h2 : Real.sqrt (comparison * delta / t) = Real.sqrt comparison * L := by
      rw [show comparison * delta / t = comparison * (delta / t) by ring]
      rw [Real.sqrt_mul (by linarith)]
    rw [h2] at h_main
    have hSlen : S_j.interval.right - S_j.interval.left = L := by
      simpa [ParameterInterval.length] using S_j.interval_length
    by_cases h : S_j.interval.right ≤ (neighbors.rectangle i).interval.right
    · have h3 : max (neighbors.rectangle i).interval.right S_j.interval.right =
          (neighbors.rectangle i).interval.right := by
        rw [max_eq_left]; exact h
      rw [h3] at h_main
      have h4 : min (neighbors.rectangle i).interval.left S_j.interval.left ≤ S_j.interval.left :=
        min_le_right _ _
      linarith
    · linarith
  -- Construct J
  let Jleft : ℝ := max 0 (S_j.interval.left - d)
  let Jright : ℝ := min 1 (S_j.interval.right + d)
  have hJleft_mem : Jleft ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : 0 ≤ Jleft := le_max_left _ _
    have h2 : Jleft ≤ S_j.interval.left := by
      exact max_le (by linarith [S_j.interval.left_mem.1]) (by linarith)
    have h3 : S_j.interval.left ≤ 1 := S_j.interval.left_mem.2
    exact ⟨h1, by linarith⟩
  have hJright_mem : Jright ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : Jright ≤ 1 := by
      dsimp only [Jright]
      have h : min (1 : ℝ) (S_j.interval.right + d) ≤ (1 : ℝ) := min_le_left _ _
      exact h
    have h2 : S_j.interval.right ≤ Jright := by
      exact le_min (by linarith [S_j.interval.right_mem.2]) (by linarith)
    have h3 : 0 ≤ S_j.interval.right := S_j.interval.right_mem.1
    exact ⟨by linarith, h1⟩
  have hJleft_le_right : Jleft ≤ Jright := by
    have h1 : Jleft ≤ S_j.interval.left := by
      exact max_le (by linarith [S_j.interval.left_mem.1]) (by linarith)
    have h2 : S_j.interval.left ≤ S_j.interval.right := S_j.interval.left_le_right
    have h3 : S_j.interval.right ≤ Jright := by
      exact le_min (by linarith [S_j.interval.right_mem.2]) (by linarith)
    linarith
  let J : ParameterInterval :=
    { left := Jleft
      right := Jright
      left_mem := hJleft_mem
      right_mem := hJright_mem
      left_le_right := hJleft_le_right }
  have hJ_len : J.length ≤ 2 * Real.sqrt comparison * L := by
    have h1 : Jleft ≥ S_j.interval.left - d := le_max_of_le_right (by linarith)
    have h2 : Jright ≤ S_j.interval.right + d := by
      dsimp only [Jright]
      have h : min (1 : ℝ) (S_j.interval.right + d) ≤ S_j.interval.right + d := min_le_right _ _
      exact h
    have hSlen : S_j.interval.right - S_j.interval.left = L := by
      simpa [ParameterInterval.length] using S_j.interval_length
    simp only [ParameterInterval.length]
    linarith
  have hJ_contains : ∀ i : Fin neighbors.card,
      (neighbors.rectangle i).interval.carrier ⊆ J.carrier := by
    intro i x hx
    have h_left1 : S_j.interval.left - d ≤ (neighbors.rectangle i).interval.left := h_hull_left i
    have h_left2 : 0 ≤ (neighbors.rectangle i).interval.left := (neighbors.rectangle i).interval.left_mem.1
    have h_gi : Jleft ≤ (neighbors.rectangle i).interval.left := by
      simp only [Jleft]
      exact max_le_iff.mpr ⟨by linarith, h_hull_left i⟩
    have h_right1 : (neighbors.rectangle i).interval.right ≤ S_j.interval.right + d := h_hull_right i
    have h_right2 : (neighbors.rectangle i).interval.right ≤ 1 := (neighbors.rectangle i).interval.right_mem.2
    have h_le : (neighbors.rectangle i).interval.right ≤ Jright := by
      simp only [Jright]
      exact le_min (by linarith) (by linarith)
    have h_x_left : Jleft ≤ (x : ℝ) := by linarith [hx.1]
    have h_x_right : (x : ℝ) ≤ Jright := by linarith [hx.2]
    exact ⟨h_x_left, h_x_right⟩
  -- Value bound
  have h_val_bound : ∀ i : Fin neighbors.card,
      ∀ x ∈ (neighbors.rectangle i).interval.carrier,
        |(neighbors.rectangle i).function x - S_j.function x| ≤ B * delta := by
    intro i x hx
    have hcomp := h_neighbors_comparable i
    have h_main := (hComp_prop comparison (by linarith)
        (neighbors.rectangle i) S_j
        (h_neighbors_centers i) hSj_family
        (h_neighbors_over i) hSj_over hcomp).2
    have h_x_in_hull : x ∈ (neighbors.rectangle i).intervalHullCarrier S_j := by
      simp only [CurvilinearRectangle.intervalHullCarrier]
      constructor
      · exact le_trans (min_le_left _ _) hx.1
      · exact le_trans hx.2 (le_max_left _ _)
    have h4 : |(neighbors.rectangle i).function x - S_j.function x| ≤
        C₁' * Real.rpow comparison 3 * delta := h_main x h_x_in_hull
    have h5 : Real.rpow comparison 3 = comparison^3 := by simp
    rw [h5] at h4
    simpa [B] using h4
  -- Carrier containment
  have h_carrier : ∀ i : Fin neighbors.card,
      (neighbors.rectangle i).carrier ⊆
        verticalNeighborhoodOn S_j.function (lambda * delta) J := by
    intro i p hp
    have h1 : p.1 ∈ (neighbors.rectangle i).interval.carrier := hp.1
    have h2 : |p.2 - (neighbors.rectangle i).function p.1| ≤ delta := hp.2
    have h3 : p.1 ∈ J.carrier := hJ_contains i h1
    have h4 : |(neighbors.rectangle i).function p.1 - S_j.function p.1| ≤ B * delta :=
      h_val_bound i p.1 h1
    have h5 : |p.2 - S_j.function p.1| ≤
        |p.2 - (neighbors.rectangle i).function p.1| +
        |(neighbors.rectangle i).function p.1 - S_j.function p.1| := by
      exact abs_sub_le _ _ _
    have h6 : |p.2 - S_j.function p.1| ≤ lambda * delta := by
      have h7 : |p.2 - S_j.function p.1| ≤ delta + B * delta := by
        calc
          |p.2 - S_j.function p.1|
            ≤ |p.2 - (neighbors.rectangle i).function p.1| +
                |(neighbors.rectangle i).function p.1 - S_j.function p.1| := h5
          _ ≤ delta + B * delta := by linarith
      have h8 : delta + B * delta = lambda * delta := by
        simp only [lambda, B]; ring
      rw [h8] at h7
      exact h7
    exact ⟨h3, h6⟩
  -- Apply generalized packing bound
  have h_pack : (neighbors.card : ℝ) ≤
      42 * lambda^2 * J.length / Real.sqrt (delta / t) :=
    generalized_packing_bound hK hI.2 hdelta hdt hlambda_100
      h_neighbors_centers h_neighbors_over h_neighbors_incomp h_neighbors_dist
      (J := J) (g := S_j.function) h_carrier
  have h_final : (neighbors.card : ℝ) ≤
      42 * lambda^2 * (2 * Real.sqrt comparison) := by
    have h2 : J.length ≤ 2 * Real.sqrt comparison * L := hJ_len
    have h3 : 0 < L := hL_pos
    calc
      (neighbors.card : ℝ)
        ≤ 42 * lambda^2 * J.length / L := h_pack
      _ ≤ 42 * lambda^2 * (2 * Real.sqrt comparison * L) / L := by gcongr
      _ = 42 * lambda^2 * (2 * Real.sqrt comparison) := by
        field_simp [h3.ne']
  simpa [lambda, B] using h_final

end Kakeya.Cinematic
