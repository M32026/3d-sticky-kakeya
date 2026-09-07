module

/-
# Rounding Wrapper for Energy Extraction

Maps an arbitrary measure on ℝ to a measure supported on the δ-grid by
nearest-neighbor rounding, and compares the regularized Riesz energies.

## Main results

1. `roundToDeltaGrid δ x` — nearest δ-grid point, error ≤ δ/2
2. `pushforwardRound δ ν` — the rounded measure
3. `rounding_kernel_comparison` — `max(dist x y, δ) ≤ 3 · max(dist (rx) (ry), δ)`
4. `rounded_energy_bound` — `I_{2κ}^δ(ν_round) ≤ 3^{2κ} · I_{2κ}^δ(ν)`
5. Grid preimage: `ν(round⁻¹(S)) = ν_round(S)` and `Nδ(round⁻¹(S)) ≤ 2 · |S|`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.MultiSetPR
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical

namespace robust_projection_main

/-- Round `x` to the nearest point on the δ-grid `δ · ℤ`. -/
def roundToDeltaGrid (δ : ℝ) (x : ℝ) : ℝ :=
  δ * (round (x / δ) : ℝ)

/-- The rounding error is at most δ/2. -/
lemma abs_sub_roundToDeltaGrid {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |x - roundToDeltaGrid δ x| ≤ δ / 2 := by
  have h1 : |x / δ - (round (x / δ) : ℝ)| ≤ 1 / 2 := abs_sub_round (x / δ)
  have h3 : x - roundToDeltaGrid δ x = δ * (x / δ - (round (x / δ) : ℝ)) := by
    dsimp only [roundToDeltaGrid]
    have h4 : δ * (x / δ - (round (x / δ) : ℝ)) = δ * (x / δ) - δ * (round (x / δ) : ℝ) := by
      rw [mul_sub]
    have h5 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
    rw [h4, h5] <;> rfl
  have h2 : |x - roundToDeltaGrid δ x| = δ * |x / δ - (round (x / δ) : ℝ)| := by
    rw [h3, abs_mul, abs_of_pos hδ]
  rw [h2]
  have h4 : δ * |x / δ - (round (x / δ) : ℝ)| ≤ δ * (1 / 2) := by
    gcongr
  have h5 : δ * (1 / 2) = δ / 2 := by ring
  rw [h5] at h4
  exact h4

/-- The rounding map is measurable. -/
lemma measurable_roundToDeltaGrid (δ : ℝ) : Measurable (roundToDeltaGrid δ) := by
  have h1 : Measurable (fun x : ℝ => x / δ) := by
    exact measurable_id.div_const δ
  have h_round : Measurable (round : ℝ → ℤ) := by
    have h_eq : (round : ℝ → ℤ) = fun x => ⌊x + 1 / 2⌋ := by
      funext x
      exact round_eq x
    rw [h_eq]
    exact Int.measurable_floor.comp (by fun_prop)
  have h2 : Measurable (fun x : ℝ => (round x : ℝ)) := by
    have h_coe : Measurable (fun z : ℤ => (z : ℝ)) := by exact Real.measurable_of_measurable_exp fun ⦃t⦄ a => trivial
    exact h_coe.comp h_round
  have h3 : Measurable (fun x : ℝ => δ * x) := by
    exact measurable_id.const_mul δ
  exact h3.comp (h2.comp h1)

/-- Pushforward of a measure under δ-grid rounding. -/
def pushforwardRound (δ : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  Measure.map (roundToDeltaGrid δ) ν

/-- **Kernel comparison under rounding**.

For any x, y, the rounded distance satisfies
`max(dist x y, δ) ≤ 3 · max(dist (rx) (ry), δ)`. -/
lemma rounding_kernel_comparison {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    max (dist x y) δ ≤ 3 * max (dist (roundToDeltaGrid δ x) (roundToDeltaGrid δ y)) δ := by
  set rx := roundToDeltaGrid δ x with hrx
  set ry := roundToDeltaGrid δ y with hry
  have h_ex : |x - rx| ≤ δ / 2 := abs_sub_roundToDeltaGrid hδ x
  have h_ey : |y - ry| ≤ δ / 2 := abs_sub_roundToDeltaGrid hδ y
  have h_tri : dist x y ≤ dist rx ry + δ := by
    have h_a : dist x y ≤ dist x rx + dist rx y := dist_triangle x rx y
    have h_b : dist rx y ≤ dist rx ry + dist ry y := dist_triangle rx ry y
    have h_c : dist x rx = |x - rx| := by
      rw [Real.dist_eq] <;> rfl
    have h_d : dist ry y = |y - ry| := by
      rw [dist_comm, Real.dist_eq] <;> rfl
    calc dist x y
      ≤ dist x rx + dist rx y := h_a
    _ ≤ dist x rx + (dist rx ry + dist ry y) := by gcongr
    _ = |x - rx| + dist rx ry + |y - ry| := by
      rw [h_c, h_d] <;> ring
    _ ≤ δ / 2 + dist rx ry + δ / 2 := by gcongr
    _ = dist rx ry + δ := by ring
  by_cases h : dist x y ≤ δ
  · -- Case 1: dist x y ≤ δ
    have h4 : max (dist x y) δ = δ := by
      rw [max_eq_right h]
    rw [h4]
    have h5 : δ ≤ 3 * max (dist rx ry) δ := by
      have h6 : δ ≤ max (dist rx ry) δ := le_max_right _ _
      linarith
    exact h5
  · -- Case 2: dist x y > δ
    have h' : δ < dist x y := by linarith
    by_cases h2 : dist rx ry ≥ δ
    · -- Subcase 2a: rounded dist ≥ δ
      have h3 : max (dist rx ry) δ = dist rx ry := by
        rw [max_eq_left h2]
      have h4 : max (dist x y) δ = dist x y := by
        rw [max_eq_left (by linarith)]
      rw [h3, h4]
      have h5 : dist x y ≤ 3 * dist rx ry := by linarith
      exact h5
    · -- Subcase 2b: rounded dist < δ
      have h2' : dist rx ry < δ := by linarith
      have h3 : max (dist rx ry) δ = δ := by
        rw [max_eq_right (by linarith)]
      rw [h3]
      have h4 : dist x y ≤ dist rx ry + δ := h_tri
      have h5 : dist x y < 2 * δ := by linarith
      have h6 : max (dist x y) δ = dist x y := by
        rw [max_eq_left (by linarith)]
      rw [h6]
      linarith

/-- **Pointwise kernel bound**.

The regularized kernel at rounded points is bounded by `3^α` times the
kernel at original points. -/
lemma rounding_pointwise_kernel_bound {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α)
    (x y : ℝ) :
    ENNReal.ofReal ((max (dist (roundToDeltaGrid δ x) (roundToDeltaGrid δ y)) δ) ^ (-α)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ α) *
        ENNReal.ofReal ((max (dist x y) δ) ^ (-α)) := by
  set d := max (dist x y) δ with hd
  set d' := max (dist (roundToDeltaGrid δ x) (roundToDeltaGrid δ y)) δ with hd'
  have hd_pos : 0 < d := by positivity
  have hd'_pos : 0 < d' := by positivity
  have h_cmp : d ≤ 3 * d' := rounding_kernel_comparison hδ x y
  have h1 : (3 * d') ^ (-α) ≤ d ^ (-α) := by
    have h_pos1 : 0 < 3 * d' := by positivity
    exact Real.rpow_le_rpow_of_nonpos hd_pos h_cmp (by linarith)
  have h2 : (3 * d') ^ (-α) = (3 : ℝ) ^ (-α) * d' ^ (-α) := by
    rw [Real.mul_rpow (by positivity) (by positivity)] <;> ring
  have h3 : (3 : ℝ) ^ (-α) * d' ^ (-α) ≤ d ^ (-α) := by
    rw [← h2] <;> exact h1
  have h4 : d' ^ (-α) ≤ (3 : ℝ) ^ α * d ^ (-α) := by
    have h5 : (3 : ℝ) ^ α * ((3 : ℝ) ^ (-α) * d' ^ (-α)) ≤ (3 : ℝ) ^ α * d ^ (-α) := by
      gcongr
    have h6 : (3 : ℝ) ^ α * (3 : ℝ) ^ (-α) = 1 := by
      have h_sum : α + (-α) = 0 := by ring
      have h : (3 : ℝ) ^ α * (3 : ℝ) ^ (-α) = (3 : ℝ) ^ (α + (-α)) := by
        rw [← Real.rpow_add (by positivity)]
      rw [h, h_sum]
      simp
    have h7 : (3 : ℝ) ^ α * ((3 : ℝ) ^ (-α) * d' ^ (-α)) = d' ^ (-α) := by
      rw [← mul_assoc, h6, one_mul]
    rw [h7] at h5
    exact h5
  have h_pos1 : 0 ≤ d' ^ (-α) := by positivity
  have h_pos2 : 0 ≤ (3 : ℝ) ^ α * d ^ (-α) := by positivity
  have h9 : ENNReal.ofReal (d' ^ (-α)) ≤ ENNReal.ofReal ((3 : ℝ) ^ α * d ^ (-α)) :=
    ENNReal.ofReal_le_ofReal h4
  have h10 : ENNReal.ofReal ((3 : ℝ) ^ α * d ^ (-α)) =
      ENNReal.ofReal ((3 : ℝ) ^ α) * ENNReal.ofReal (d ^ (-α)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [h10] at h9
  exact h9

/-- **Regularized energy bound under rounding**.

`I_{2κ}^δ(ν_round) ≤ 3^{2κ} · I_{2κ}^δ(ν)`. -/
lemma rounded_energy_bound {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] :
    rieszEnergy (2 * κ) hδ (pushforwardRound δ ν) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (2 * κ)) * rieszEnergy (2 * κ) hδ ν := by
  set α := 2 * κ with hα_def
  have hα_pos : 0 < α := by positivity
  set f := roundToDeltaGrid δ with hf_def
  have hf_meas : Measurable f := measurable_roundToDeltaGrid δ
  set ν' := pushforwardRound δ ν with hν'_def
  let k : ℝ → ℝ → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α))
  have hk_meas : Measurable (fun p : ℝ × ℝ => k p.1 p.2) := by fun_prop
  have hk_meas_f : ∀ (x : ℝ), Measurable (fun y : ℝ => k x y) := by
    intro x
    have h1 : Measurable (fun y : ℝ => dist x y) :=
      measurable_const.dist measurable_id
    have h2 : Measurable (fun y : ℝ => max (dist x y) δ) :=
      h1.max measurable_const
    have h3 : Measurable (fun y : ℝ => (max (dist x y) δ) ^ (-α)) := by fun_prop
    exact measurable_ofReal.comp h3
  have h_main1 : ∫⁻ (x' : ℝ), ∫⁻ (y' : ℝ), k x' y' ∂ν' ∂ν' =
      ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ∂ν := by
    let g1 : ℝ → ENNReal := fun x' => ∫⁻ (y' : ℝ), k x' y' ∂(Measure.map f ν)
    have hg1_meas : Measurable g1 := by
      letI : SFinite (Measure.map f ν) := inferInstance
      exact Measurable.lintegral_prod_right hk_meas
    have h_step1 : ∫⁻ (x' : ℝ), ∫⁻ (y' : ℝ), k x' y' ∂ν' ∂ν' = ∫⁻ (x' : ℝ), g1 x' ∂ν' := by
      rfl
    calc ∫⁻ (x' : ℝ), ∫⁻ (y' : ℝ), k x' y' ∂ν' ∂ν'
      = ∫⁻ (x' : ℝ), g1 x' ∂ν' := h_step1
    _ = ∫⁻ (x : ℝ), g1 (f x) ∂ν := MeasureTheory.lintegral_map hg1_meas hf_meas
    _ = ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ∂ν := by
        congr with x
        have hν'_eq2 : ν' = Measure.map f ν := by
          simpa [ν', pushforwardRound, hf_def] using rfl
        have h_goal : ∫⁻ (y' : ℝ), k (f x) y' ∂ν' = ∫⁻ (y : ℝ), k (f x) (f y) ∂ν := by
          convert MeasureTheory.lintegral_map (hk_meas_f (f x)) hf_meas using 1
          <;> rw [hν'_eq2]
        exact h_goal
  have h_pointwise : ∀ (x y : ℝ), k (f x) (f y) ≤
      ENNReal.ofReal ((3 : ℝ) ^ α) * k x y := by
    intro x y
    exact rounding_pointwise_kernel_bound hδ hα_pos x y
  have h_inner : ∀ (x : ℝ), ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ≤
      ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (y : ℝ), k x y ∂ν := by
    intro x
    have h3 : ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ≤
        ∫⁻ (y : ℝ), (ENNReal.ofReal ((3 : ℝ) ^ α) * k x y) ∂ν := by
      apply lintegral_mono
      intro y
      exact h_pointwise x y
    have h4 : ∫⁻ (y : ℝ), (ENNReal.ofReal ((3 : ℝ) ^ α) * k x y) ∂ν =
        ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (y : ℝ), k x y ∂ν := by
      rw [MeasureTheory.lintegral_const_mul _ (hk_meas_f x)]
    rw [h4] at h3
    exact h3
  have h_outer : ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ∂ν ≤
      ∫⁻ (x : ℝ), (ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (y : ℝ), k x y ∂ν) ∂ν := by
    apply lintegral_mono
    intro x
    exact h_inner x
  let g : ℝ → ENNReal := fun x => ∫⁻ (y : ℝ), k x y ∂ν
  have hg_meas : Measurable g := hk_meas.lintegral_prod_right
  have h_final : ∫⁻ (x : ℝ), (ENNReal.ofReal ((3 : ℝ) ^ α) * g x) ∂ν =
      ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (x : ℝ), g x ∂ν := by
    rw [MeasureTheory.lintegral_const_mul _ hg_meas]
  have h_result : ∫⁻ (x' : ℝ), ∫⁻ (y' : ℝ), k x' y' ∂ν' ∂ν' ≤
      ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k x y ∂ν ∂ν := by
    calc ∫⁻ (x' : ℝ), ∫⁻ (y' : ℝ), k x' y' ∂ν' ∂ν'
      = ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k (f x) (f y) ∂ν ∂ν := h_main1
    _ ≤ ∫⁻ (x : ℝ), (ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (y : ℝ), k x y ∂ν) ∂ν := h_outer
    _ = ENNReal.ofReal ((3 : ℝ) ^ α) * ∫⁻ (x : ℝ), ∫⁻ (y : ℝ), k x y ∂ν ∂ν := h_final
  simpa [rieszEnergy, k] using h_result

/-- Distinct 1D dyadic cubes at the same scale are disjoint. -/
lemma dyadic_cubes_disjoint {δ : ℝ} (hδ : 0 < δ) {k1 k2 : ℤ} (h : k1 ≠ k2) :
    Disjoint (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 + 1 : ℤ) : ℝ)))
      (Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 + 1 : ℤ) : ℝ))) := by
  have h_main : ∀ (a b : ℤ), a < b → Disjoint (Set.Ico (δ * (a : ℝ)) (δ * ((a + 1 : ℤ) : ℝ)))
      (Set.Ico (δ * (b : ℝ)) (δ * ((b + 1 : ℤ) : ℝ))) := by
    intro a b hab
    have h3 : (a + 1 : ℤ) ≤ b := by linarith
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h4 : x < δ * ((a + 1 : ℤ) : ℝ) := hx1.2
    have h5 : δ * (b : ℝ) ≤ x := hx2.1
    have h6 : δ * ((a + 1 : ℤ) : ℝ) ≤ δ * (b : ℝ) := by
      gcongr <;> norm_cast <;> linarith
    linarith
  by_cases h' : k1 < k2
  · exact h_main k1 k2 h'
  · have h'' : k2 < k1 := by omega
    exact (h_main k2 k1 h'').symm

/-- A single dyadic cube has covering number ≤ 1. -/
lemma single_dyadic_cube_covering_one {δ : ℝ} (hδ : 0 < δ) (n : ℤ) :
    Nreal δ (Set.Ico (δ * (n : ℝ)) (δ * ((n + 1 : ℤ) : ℝ))) ≤ 1 := by
  dsimp only [Nreal]
  let kn : Fin 1 → ℤ := fun _ => n
  have hP_eq : realLineCopy (Set.Ico (δ * (n : ℝ)) (δ * ((n + 1 : ℤ) : ℝ))) =
      dyadicCube δ kn := by
    ext x
    simp [realLineCopy, dyadicCube, kn] <;> rfl
  rw [hP_eq]
  have h1 : ∀ (Q : Set (EuclideanSpace ℝ (Fin 1))),
      Q ∈ dyadicCubesMeeting δ (dyadicCube δ kn) → Q = dyadicCube δ kn := by
    intro Q hQ
    rcases hQ with ⟨⟨k, rfl⟩, h_nonempty⟩
    have h2 : (dyadicCube δ k ∩ dyadicCube δ kn).Nonempty := h_nonempty
    by_cases h3 : k = kn
    · rw [h3]
    · have h4 : k 0 ≠ kn 0 := by
        intro h5
        have h6 : k = kn := by
          funext i
          fin_cases i <;> exact h5
        exact h3 h6
      have h5 : Disjoint (dyadicCube δ k) (dyadicCube δ kn) := by
        have h6 : Disjoint (Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 + 1 : ℤ) : ℝ)))
            (Set.Ico (δ * (kn 0 : ℝ)) (δ * ((kn 0 + 1 : ℤ) : ℝ))) :=
          dyadic_cubes_disjoint hδ h4
        rw [Set.disjoint_left] at h6 ⊢
        intro z hz1 hz2
        have h71 : z 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 + 1 : ℤ) : ℝ)) := by
          have h7 := hz1 0
          simpa [add_assoc] using h7
        have h81 : z 0 ∈ Set.Ico (δ * (kn 0 : ℝ)) (δ * ((kn 0 + 1 : ℤ) : ℝ)) := by
          have h8 := hz2 0
          simpa [add_assoc] using h8
        exact h6 h71 h81
      have h_contra : (dyadicCube δ k ∩ dyadicCube δ kn) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h5
      rw [h_contra] at h2
      simpa using h2
  have h2 : dyadicCubesMeeting δ (dyadicCube δ kn) ⊆ {dyadicCube δ kn} := by
    intro Q hQ
    exact h1 Q hQ ▸ Set.mem_singleton _
  have h3 : (dyadicCubesMeeting δ (dyadicCube δ kn)).encard ≤ 1 := by
    have h4 := Set.encard_mono h2
    rw [Set.encard_singleton] at h4
    exact h4
  exact_mod_cast h3

/-- Covering number monotonicity. -/
lemma Nreal_mono_local {δ : ℝ} {A B : Set ℝ} (h : A ⊆ B) : Nreal δ A ≤ Nreal δ B := by
  dsimp only [Nreal, dyadicCoveringNumber]
  have h1 : realLineCopy A ⊆ realLineCopy B := by
    intro x hx
    exact h hx
  have h2 : dyadicCubesMeeting δ (realLineCopy A) ⊆ dyadicCubesMeeting δ (realLineCopy B) := by
    intro Q hQ
    exact ⟨hQ.1, Set.Nonempty.mono (Set.inter_subset_inter_right _ h1) hQ.2⟩
  exact_mod_cast Set.encard_mono h2

/-- A single rounding cell is contained in two adjacent dyadic cubes. -/
lemma single_cell_covering_le_two {δ : ℝ} (hδ : 0 < δ) (n : ℤ) :
    Nreal δ {x : ℝ | roundToDeltaGrid δ x = δ * (n : ℝ)} ≤ 2 := by
  have h_cell_eq : {x : ℝ | roundToDeltaGrid δ x = δ * (n : ℝ)} =
      Set.Ico (δ * (n : ℝ) - δ / 2) (δ * (n : ℝ) + δ / 2) := by
    ext x
    simp only [roundToDeltaGrid, Set.mem_setOf_eq, Set.mem_Ico]
    have h2 : δ * (round (x / δ) : ℝ) = δ * (n : ℝ) ↔
        (round (x / δ) : ℝ) = (n : ℝ) := by
      constructor
      · intro h; exact (mul_right_inj' hδ.ne').mp h
      · intro h; rw [h]
    have h3 : (round (x / δ) : ℝ) = (n : ℝ) ↔ round (x / δ) = n := by
      exact_mod_cast Iff.rfl
    have h4 : round (x / δ) = n ↔
        (n : ℝ) - 1 / 2 ≤ x / δ ∧ x / δ < (n : ℝ) + 1 / 2 := by
      rw [round_eq_iff]
      simp [Set.mem_Ico]
      <;> ring
    have h5 : ((n : ℝ) - 1 / 2 ≤ x / δ ∧ x / δ < (n : ℝ) + 1 / 2) ↔
        (δ * (n : ℝ) - δ / 2 ≤ x ∧ x < δ * (n : ℝ) + δ / 2) := by
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · have h6 : δ * ((n : ℝ) - 1 / 2) ≤ δ * (x / δ) := by gcongr
          have h7 : δ * ((n : ℝ) - 1 / 2) = δ * (n : ℝ) - δ / 2 := by ring
          have h8 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
          rw [h7, h8] at h6; exact h6
        · have h6 : δ * (x / δ) < δ * ((n : ℝ) + 1 / 2) := by gcongr
          have h7 : δ * ((n : ℝ) + 1 / 2) = δ * (n : ℝ) + δ / 2 := by ring
          have h8 : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
          rw [h7, h8] at h6; exact h6
      · rintro ⟨h1, h2⟩
        constructor
        · have h6 : (n : ℝ) - 1 / 2 ≤ x / δ := by
            have h7 : δ * ((n : ℝ) - 1 / 2) ≤ x := by
              have h8 : δ * ((n : ℝ) - 1 / 2) = δ * (n : ℝ) - δ / 2 := by ring
              rw [h8]; exact h1
            have h9 : δ * ((n : ℝ) - 1 / 2) = δ * ((n : ℝ) - 1 / 2) := rfl
            have h10 : (n : ℝ) - 1 / 2 ≤ x / δ := by
              calc (n : ℝ) - 1 / 2
                = (δ * ((n : ℝ) - 1 / 2)) / δ := by field_simp [hδ.ne'] <;> ring
              _ ≤ x / δ := by gcongr
            exact h10
          exact h6
        · have h6 : x / δ < (n : ℝ) + 1 / 2 := by
            have h7 : x < δ * ((n : ℝ) + 1 / 2) := by
              have h8 : δ * ((n : ℝ) + 1 / 2) = δ * (n : ℝ) + δ / 2 := by ring
              rw [h8]; exact h2
            calc x / δ
              < (δ * ((n : ℝ) + 1 / 2)) / δ := by gcongr
            _ = (n : ℝ) + 1 / 2 := by field_simp [hδ.ne'] <;> ring
          exact h6
    rw [h2, h3, h4, h5]
  rw [h_cell_eq]
  let Q1 := Set.Ico (δ * ((n - 1 : ℤ) : ℝ)) (δ * (n : ℝ))
  let Q2 := Set.Ico (δ * (n : ℝ)) (δ * ((n + 1 : ℤ) : ℝ))
  have h_sub : Set.Ico (δ * (n : ℝ) - δ / 2) (δ * (n : ℝ) + δ / 2) ⊆ Q1 ∪ Q2 := by
    intro x hx
    have h1 : δ * (n : ℝ) - δ / 2 ≤ x := hx.1
    have h2 : x < δ * (n : ℝ) + δ / 2 := hx.2
    by_cases h3 : x < δ * (n : ℝ)
    · have h4 : δ * ((n - 1 : ℤ) : ℝ) ≤ x := by
        have h5 : δ * ((n - 1 : ℤ) : ℝ) = δ * (n : ℝ) - δ := by
          simp [sub_eq_add_neg] <;> ring
        rw [h5]
        linarith
      exact Or.inl ⟨h4, h3⟩
    · have h4 : δ * (n : ℝ) ≤ x := by linarith
      have h5 : x < δ * ((n + 1 : ℤ) : ℝ) := by
        have h6 : δ * ((n + 1 : ℤ) : ℝ) = δ * (n : ℝ) + δ := by
          simp [add_assoc] <;> ring
        rw [h6]
        linarith
      exact Or.inr ⟨h4, h5⟩
  have h1 : Nreal δ (Set.Ico (δ * (n : ℝ) - δ / 2) (δ * (n : ℝ) + δ / 2)) ≤ Nreal δ (Q1 ∪ Q2) :=
    Nreal_mono_local h_sub
  have h2 : Nreal δ (Q1 ∪ Q2) ≤ Nreal δ Q1 + Nreal δ Q2 := by
    dsimp only [Nreal]
    have h1 : realLineCopy (Q1 ∪ Q2) = realLineCopy Q1 ∪ realLineCopy Q2 := by
      ext z; simp [realLineCopy]
    rw [h1]
    have h_main : (dyadicCubesMeeting δ (realLineCopy Q1 ∪ realLineCopy Q2)).encard ≤
        (dyadicCubesMeeting δ (realLineCopy Q1)).encard +
        (dyadicCubesMeeting δ (realLineCopy Q2)).encard := by
      have h_sub : dyadicCubesMeeting δ (realLineCopy Q1 ∪ realLineCopy Q2) ⊆
          dyadicCubesMeeting δ (realLineCopy Q1) ∪ dyadicCubesMeeting δ (realLineCopy Q2) := by
        intro Q hQ
        rcases hQ with ⟨hQ_cube, ⟨x, hx⟩⟩
        have h_x_in : x ∈ realLineCopy Q1 ∨ x ∈ realLineCopy Q2 := hx.2
        rcases h_x_in with (h_x_in | h_x_in)
        · exact Or.inl ⟨hQ_cube, ⟨x, hx.1, h_x_in⟩⟩
        · exact Or.inr ⟨hQ_cube, ⟨x, hx.1, h_x_in⟩⟩
      calc (dyadicCubesMeeting δ (realLineCopy Q1 ∪ realLineCopy Q2)).encard
        ≤ (dyadicCubesMeeting δ (realLineCopy Q1) ∪ dyadicCubesMeeting δ (realLineCopy Q2)).encard :=
          Set.encard_mono h_sub
      _ ≤ (dyadicCubesMeeting δ (realLineCopy Q1)).encard +
            (dyadicCubesMeeting δ (realLineCopy Q2)).encard :=
          Set.encard_union_le _ _
    exact_mod_cast h_main
  have hQ1 : Nreal δ Q1 ≤ 1 := by
    simpa [Q1] using single_dyadic_cube_covering_one hδ (n - 1)
  have hQ2 : Nreal δ Q2 ≤ 1 := by
    simpa [Q2] using single_dyadic_cube_covering_one hδ n
  calc Nreal δ (Set.Ico (δ * (n : ℝ) - δ / 2) (δ * (n : ℝ) + δ / 2))
    ≤ Nreal δ (Q1 ∪ Q2) := h1
  _ ≤ Nreal δ Q1 + Nreal δ Q2 := h2
  _ ≤ 1 + 1 := by gcongr
  _ = 2 := by norm_num

/-- Covering numbers are subadditive over finite unions indexed by any type. -/
lemma covering_union_finset {δ : ℝ} {α : Type*} (s : Finset α) (f : α → Set ℝ) :
    Nreal δ (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, Nreal δ (f i) := by
  induction s using Finset.induction with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset α), f i) = (∅ : Set ℝ) := by simp
    rw [h]
    have h_empty : Nreal δ (∅ : Set ℝ) = 0 := by
      have h1 : realLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
        ext z; simp [realLineCopy]
      simp [Nreal, dyadicCoveringNumber, dyadicCubesMeeting, h1]
    rw [h_empty] <;> simp
  | @insert a s ha ih =>
    have h1 : (⋃ i ∈ (insert a s), f i) = (f a) ∪ (⋃ i ∈ s, f i) := by
      ext x
      simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union]
      <;> aesop
    rw [h1, Finset.sum_insert ha]
    have h_cov2 : Nreal δ (f a ∪ (⋃ i ∈ s, f i)) ≤ Nreal δ (f a) + Nreal δ (⋃ i ∈ s, f i) := by
      dsimp only [Nreal]
      have h1 : realLineCopy (f a ∪ (⋃ i ∈ s, f i)) =
          realLineCopy (f a) ∪ realLineCopy (⋃ i ∈ s, f i) := by
        ext z; simp [realLineCopy]
      rw [h1]
      have h_main : (dyadicCubesMeeting δ (realLineCopy (f a) ∪ realLineCopy (⋃ i ∈ s, f i))).encard ≤
          (dyadicCubesMeeting δ (realLineCopy (f a))).encard +
          (dyadicCubesMeeting δ (realLineCopy (⋃ i ∈ s, f i))).encard := by
        have h_sub : dyadicCubesMeeting δ (realLineCopy (f a) ∪ realLineCopy (⋃ i ∈ s, f i)) ⊆
            dyadicCubesMeeting δ (realLineCopy (f a)) ∪
            dyadicCubesMeeting δ (realLineCopy (⋃ i ∈ s, f i)) := by
          intro Q hQ
          rcases hQ with ⟨hQ_cube, ⟨x, hx1, hx2⟩⟩
          rcases hx2 with (h2 | h2)
          · exact Or.inl ⟨hQ_cube, ⟨x, hx1, h2⟩⟩
          · exact Or.inr ⟨hQ_cube, ⟨x, hx1, h2⟩⟩
        calc (dyadicCubesMeeting δ (realLineCopy (f a) ∪ realLineCopy (⋃ i ∈ s, f i))).encard
          ≤ (dyadicCubesMeeting δ (realLineCopy (f a)) ∪
                dyadicCubesMeeting δ (realLineCopy (⋃ i ∈ s, f i))).encard :=
            Set.encard_mono h_sub
        _ ≤ (dyadicCubesMeeting δ (realLineCopy (f a))).encard +
              (dyadicCubesMeeting δ (realLineCopy (⋃ i ∈ s, f i))).encard :=
            Set.encard_union_le _ _
      exact_mod_cast h_main
    exact le_trans h_cov2 (add_le_add_right ih _)

/-- **Grid preimage measure equality**.

If `A_cells = round⁻¹(S)`, then `ν(A_cells) = ν_round(S)`. -/
lemma grid_preimage_measure {δ : ℝ} {ν : Measure ℝ} {S : Set ℝ}
    (hS_meas : MeasurableSet S) :
    ν ((roundToDeltaGrid δ) ⁻¹' S) = (pushforwardRound δ ν) S := by
  dsimp only [pushforwardRound]
  exact (Measure.map_apply (measurable_roundToDeltaGrid δ) hS_meas).symm

/-- **Grid preimage covering bound**.

If `S ⊆ δℤ` is a δ-grid set, then `Nδ(round⁻¹(S)) ≤ 2 · |S|`. -/
lemma grid_preimage_covering_bound {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_grid : S ⊆ productLikeIntegerGrid δ) :
    Nreal δ ((roundToDeltaGrid δ) ⁻¹' S) ≤ 2 * ENat.toENNReal S.encard := by
  by_cases hS_inf : Set.Infinite S
  · have h_top : S.encard = ⊤ := by
      exact encard_eq_top_iff.mpr hS_inf
    rw [h_top] <;> simp
  · have hS_finite : Set.Finite S := by exact not_infinite.mp hS_inf
    let sFinset := hS_finite.toFinset
    have hS_eq : S = ↑sFinset := by
      simp [sFinset, hS_finite.coe_toFinset]
    have h_preimage_eq : (roundToDeltaGrid δ) ⁻¹' S = ⋃ y ∈ sFinset, (roundToDeltaGrid δ) ⁻¹' {y} := by
      rw [hS_eq]
      ext x
      simp [sFinset, Set.mem_iUnion]
      <;> aesop
    rw [h_preimage_eq]
    have h_main : Nreal δ (⋃ y ∈ sFinset, (roundToDeltaGrid δ) ⁻¹' {y}) ≤
        ∑ y ∈ sFinset, Nreal δ ((roundToDeltaGrid δ) ⁻¹' {y}) :=
      covering_union_finset sFinset (fun y => (roundToDeltaGrid δ) ⁻¹' {y})
    have h_each : ∀ y ∈ sFinset, Nreal δ ((roundToDeltaGrid δ) ⁻¹' {y}) ≤ 2 := by
      intro y hy
      have hyS : y ∈ S := by
        simpa [sFinset, hS_finite.coe_toFinset] using hy
      have hy_grid : y ∈ productLikeIntegerGrid δ := hS_grid hyS
      rcases hy_grid with ⟨n, rfl⟩
      have h_set_eq : (roundToDeltaGrid δ) ⁻¹' {δ * (n : ℝ)} =
          {x : ℝ | roundToDeltaGrid δ x = δ * (n : ℝ)} := by
        ext x
        simp
      rw [h_set_eq]
      exact single_cell_covering_le_two hδ n
    have h_sum : ∑ y ∈ sFinset, Nreal δ ((roundToDeltaGrid δ) ⁻¹' {y}) ≤ ∑ y ∈ sFinset, (2 : ENNReal) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_each i ‹_›
    have h_sum2 : ∑ y ∈ sFinset, (2 : ENNReal) = 2 * (sFinset.card : ENNReal) := by
      simp [Finset.sum_const] <;> ring
    have h_encard : S.encard = (sFinset.card : ENat) := by
      rw [hS_eq]
      simp
    calc Nreal δ (⋃ y ∈ sFinset, (roundToDeltaGrid δ) ⁻¹' {y})
      ≤ ∑ y ∈ sFinset, Nreal δ ((roundToDeltaGrid δ) ⁻¹' {y}) := h_main
    _ ≤ ∑ y ∈ sFinset, (2 : ENNReal) := h_sum
    _ = 2 * (sFinset.card : ENNReal) := h_sum2
    _ = 2 * ENat.toENNReal S.encard := by
      rw [h_encard] <;> rfl

/-- A bounded subset of the δ-grid is finite. -/
lemma bounded_grid_subset_finite {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_grid : S ⊆ productLikeIntegerGrid δ) (hS_bdd : Bornology.IsBounded S) :
    Set.Finite S := by
  have h2 : ∃ (r : ℝ), S ⊆ Metric.closedBall (0 : ℝ) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hS_bdd
  rcases h2 with ⟨r, hr⟩
  let I : Set ℤ := Set.Icc (⌊-r / δ⌋) (⌈r / δ⌉)
  have hI_finite : Set.Finite I := Set.finite_Icc _ _
  have h3 : S ⊆ (fun n : ℤ => δ * (n : ℝ)) '' I := by
    intro y hy
    have h4 : y ∈ productLikeIntegerGrid δ := hS_grid hy
    rcases h4 with ⟨n, rfl⟩
    have h5 : dist (0 : ℝ) (δ * (n : ℝ)) ≤ r := by
      have h51 : (δ * (n : ℝ)) ∈ Metric.closedBall (0 : ℝ) r := hr hy
      simpa [Metric.mem_closedBall] using h51
    have h6 : |δ * (n : ℝ)| ≤ r := by simpa [Real.dist_eq, abs_zero] using h5
    have h7 : -r ≤ δ * (n : ℝ) := (abs_le.mp h6).1
    have h8 : δ * (n : ℝ) ≤ r := (abs_le.mp h6).2
    have h9 : (n : ℝ) ≥ -r / δ := by
      calc (n : ℝ) = (δ * (n : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≥ (-r) / δ := by gcongr
        _ = -r / δ := by ring
    have h10 : (n : ℝ) ≤ r / δ := by
      calc (n : ℝ) = (δ * (n : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ r / δ := by gcongr
    have h11 : ⌊-r / δ⌋ ≤ n := by
      have h12 : (⌊-r / δ⌋ : ℝ) ≤ -r / δ := Int.floor_le (-r / δ)
      have h13 : (⌊-r / δ⌋ : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast h13
    have h13 : n ≤ ⌈r / δ⌉ := by
      have h14 : (r / δ : ℝ) ≤ ⌈r / δ⌉ := Int.le_ceil (r / δ)
      have h15 : (n : ℝ) ≤ (⌈r / δ⌉ : ℝ) := by linarith
      exact_mod_cast h15
    have h15 : n ∈ I := ⟨h11, h13⟩
    exact ⟨n, h15, rfl⟩
  exact Set.Finite.subset (Set.Finite.image _ hI_finite) h3

/-- **Finite support package for the rounded measure**.

If ν is a probability measure with bounded support, then ν_delta = (roundToDeltaGrid δ)#ν
is supported on a finite δ-separated grid set Gδ. -/
lemma rounded_measure_finite_support_package {δ : ℝ} (hδ : 0 < δ) {ν : Measure ℝ}
    [IsProbabilityMeasure ν]
    (h_support_bdd : Bornology.IsBounded (ν.support)) :
    ∃ (Gδ : Set ℝ), Set.Finite Gδ ∧
      (pushforwardRound δ ν) Set.univ = 1 ∧
      (pushforwardRound δ ν).support ⊆ Gδ ∧
      ∀ (x y : ℝ), x ∈ Gδ → y ∈ Gδ → x ≠ y → dist x y ≥ δ := by
  let f := roundToDeltaGrid δ
  let Gδ := f '' ν.support
  have hf_meas : Measurable f := measurable_roundToDeltaGrid δ
  have hGδ_grid : Gδ ⊆ productLikeIntegerGrid δ := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have h_goal : f u = δ * (round (u / δ) : ℝ) := by
      dsimp only [f, roundToDeltaGrid] <;> rfl
    rw [h_goal]
    exact ⟨round (u / δ), by ring⟩
  have h2_bdd : ∃ (r : ℝ), ν.support ⊆ Metric.closedBall (0 : ℝ) r :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp h_support_bdd
  rcases h2_bdd with ⟨r, hr⟩
  have hGδ_bdd : Bornology.IsBounded Gδ := by
    have h1 : Gδ ⊆ Metric.closedBall (0 : ℝ) (r + δ / 2) := by
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      have h2 : dist (0 : ℝ) u ≤ r := by
        simpa [Metric.mem_closedBall] using hr hu
      have h4 : dist (0 : ℝ) (f u) ≤ dist (0 : ℝ) u + dist u (f u) := dist_triangle 0 u (f u)
      have h5 : dist u (f u) ≤ δ / 2 := by
        have h6 : dist u (f u) = |u - f u| := by
          simp [Real.dist_eq]
        rw [h6]
        exact abs_sub_roundToDeltaGrid hδ u
      have h7 : dist (0 : ℝ) (f u) ≤ r + δ / 2 := by linarith
      simpa [Metric.mem_closedBall] using h7
    have h_main : ∃ (r' : ℝ), Gδ ⊆ Metric.closedBall (0 : ℝ) r' := ⟨r + δ / 2, h1⟩
    exact (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mpr h_main
  have hGδ_finite : Set.Finite Gδ := bounded_grid_subset_finite hδ hGδ_grid hGδ_bdd
  set ν' := pushforwardRound δ ν with hν'_def
  have h_mass : ν' Set.univ = 1 := by
    dsimp only [ν', pushforwardRound]
    have h_map : Measure.map f ν Set.univ = ν Set.univ := by
      rw [Measure.map_apply hf_meas MeasurableSet.univ]
      <;> simp
    rw [h_map, measure_univ]
  have h_preimage_subset : f ⁻¹' (Gδᶜ) ⊆ (ν.support)ᶜ := by
    intro u hu
    have h3 : f u ∉ Gδ := hu
    by_contra h4
    have h4' : u ∈ ν.support := by simpa [Set.mem_compl_iff] using h4
    have h5 : f u ∈ Gδ := ⟨u, h4', rfl⟩
    exact h3 h5
  have h_null : ν (f ⁻¹' (Gδᶜ)) = 0 := by
    have h6 : ν (f ⁻¹' (Gδᶜ)) ≤ ν ((ν.support)ᶜ) := measure_mono h_preimage_subset
    have h7 : ν ((ν.support)ᶜ) = 0 := ν.measure_compl_support
    have h8 : ν (f ⁻¹' (Gδᶜ)) ≤ 0 := le_trans h6 (le_of_eq h7)
    exact le_zero_iff.mp h8
  have hGδ_closed : IsClosed Gδ := hGδ_finite.isClosed
  have hGδc_meas : MeasurableSet (Gδᶜ) := hGδ_closed.isOpen_compl.measurableSet
  have h_pushforward_null : ν' Gδᶜ = 0 := by
    dsimp only [ν', pushforwardRound]
    rw [Measure.map_apply hf_meas hGδc_meas]
    exact h_null
  have h_ae : Gδ ∈ MeasureTheory.ae ν' := by
    simpa [MeasureTheory.mem_ae_iff] using h_pushforward_null
  have h_support : ν'.support ⊆ Gδ :=
    MeasureTheory.Measure.support_subset_of_isClosed hGδ_closed h_ae
  have h_separated : ∀ (x y : ℝ), x ∈ Gδ → y ∈ Gδ → x ≠ y → dist x y ≥ δ := by
    intro x y hx hy hxy
    have hxg : x ∈ productLikeIntegerGrid δ := hGδ_grid hx
    have hyg : y ∈ productLikeIntegerGrid δ := hGδ_grid hy
    rcases hxg with ⟨n, hnx⟩
    rcases hyg with ⟨m, hmy⟩
    have hnm : n ≠ m := by
      intro h
      have h1 : x = y := by
        calc x = δ * (n : ℝ) := hnx
          _ = δ * (m : ℝ) := by rw [h]
          _ = y := hmy.symm
      exact hxy h1
    have h9 : |(n : ℝ) - (m : ℝ)| ≥ 1 := by
      have h10 : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
      have h11 : |n - m| ≥ 1 := by
        apply Int.one_le_abs
        omega
      have h12 : |(n : ℝ) - (m : ℝ)| = |(n - m : ℤ)| := by
        norm_cast
      rw [h12]
      exact_mod_cast h11
    calc dist x y
      = dist (δ * (n : ℝ)) (δ * (m : ℝ)) := by rw [hnx, hmy]
    _ = |δ * (n : ℝ) - δ * (m : ℝ)| := by rw [Real.dist_eq]
    _ = |δ * ((n : ℝ) - (m : ℝ))| := by ring_nf
    _ = |δ| * |(n : ℝ) - (m : ℝ)| := by rw [abs_mul]
    _ = δ * |(n : ℝ) - (m : ℝ)| := by rw [abs_of_pos hδ]
    _ ≥ δ * 1 := by gcongr
    _ = δ := by ring
  exact ⟨Gδ, hGδ_finite, h_mass, h_support, h_separated⟩

/-- **Reverse comparison**: `card(S) ≤ Nδ(Rδ^(-1)(S))`.

Each grid point `y ∈ S` lies in a distinct δ-dyadic cube, and that cube
meets the rounding cell of `y`, hence meets `A_cells`. -/
lemma grid_card_le_Ndelta_cells {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_grid : S ⊆ productLikeIntegerGrid δ) (hS_finite : Set.Finite S) :
    ENat.toENNReal S.encard ≤ Nreal δ ((roundToDeltaGrid δ) ⁻¹' S) := by
  choose n hn using fun (y : ℝ) (hy : y ∈ S) => hS_grid hy
  -- Total function n' : ℝ → ℤ, agrees with n on S
  let n' : ℝ → ℤ := fun y => if h : y ∈ S then n y h else 0
  let f : ℝ → Set (EuclideanSpace ℝ (Fin 1)) := fun y =>
    dyadicCube δ (fun (_ : Fin 1) => n' y)
  let pt : ℝ → EuclideanSpace ℝ (Fin 1) := fun y => (WithLp.equiv 2 _).symm (fun _ => y)
  have hpt_eval : ∀ (y : ℝ), (pt y) 0 = y := by
    intro y
    simp [pt]

  have hn'_eq : ∀ (y : ℝ) (hy : y ∈ S), n' y = n y hy := by
    intro y hy
    simp [n', hy]
  have h_y_eq : ∀ (y : ℝ) (hy : y ∈ S), y = δ * (n' y : ℝ) := by
    intro y hy
    rw [hn'_eq y hy]
    exact hn y hy
  have h_round_id : ∀ (y : ℝ) (hy : y ∈ S), roundToDeltaGrid δ y = y := by
    intro y hy
    have h_y : y = δ * (n' y : ℝ) := h_y_eq y hy
    rw [h_y]
    dsimp only [roundToDeltaGrid]
    have h3 : (δ * (n' y : ℝ)) / δ = (n' y : ℝ) := by
      field_simp [hδ.ne'] <;> ring
    rw [h3]
    have h4 : round (n' y : ℝ) = (n' y : ℤ) := by simp
    rw [h4] <;> norm_cast

  have h_meets : ∀ y ∈ S, f y ∈ dyadicCubesMeeting δ (realLineCopy ((roundToDeltaGrid δ) ⁻¹' S)) := by
    intro y hy
    have h1 : f y ∈ dyadicCubes 1 δ := by exact ⟨_, rfl⟩
    have h2 : (f y ∩ realLineCopy ((roundToDeltaGrid δ) ⁻¹' S)).Nonempty := by
      use pt y
      constructor
      · -- pt y ∈ f y
        have h_y : y = δ * (n' y : ℝ) := h_y_eq y hy
        have h_goal : y ∈ Set.Ico (δ * (n' y : ℝ)) (δ * ((n' y : ℝ) + 1)) := by
          have h_left : δ * (n' y : ℝ) ≤ y := le_of_eq h_y.symm
          have h_right : y < δ * ((n' y : ℝ) + 1) := by
            calc y = δ * (n' y : ℝ) := h_y
              _ < δ * ((n' y : ℝ) + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
          exact ⟨h_left, h_right⟩
        intro i; fin_cases i
        simpa [pt, f] using h_goal
      · -- pt y ∈ realLineCopy (...)
        simp only [realLineCopy, Set.mem_setOf_eq]
        have h3 : roundToDeltaGrid δ y ∈ S := by
          rw [h_round_id y hy] <;> exact hy
        have h4 : (pt y) 0 ∈ (roundToDeltaGrid δ) ⁻¹' S := by
          rw [hpt_eval y] <;> simpa using h3
        exact h4
    exact ⟨h1, h2⟩

  have h_cube_inj : ∀ (a b : ℤ),
      dyadicCube δ (fun (_ : Fin 1) => a) = dyadicCube δ (fun (_ : Fin 1) => b) → a = b := by
    intro a b h_eq
    let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 _).symm (fun _ => δ * (a : ℝ))
    have hp_eval : p 0 = δ * (a : ℝ) := by simp [p]
    have h3 : p ∈ dyadicCube δ (fun (_ : Fin 1) => a) := by
      intro i; fin_cases i
      have h_goal : δ * (a : ℝ) ∈ Set.Ico (δ * (a : ℝ)) (δ * ((a : ℝ) + 1)) := by
        exact ⟨by linarith, by linarith [hδ]⟩
      simpa [p, dyadicCube] using h_goal
    have h4 : p ∈ dyadicCube δ (fun (_ : Fin 1) => b) := by
      exact h_eq ▸ h3
    have h5 : p 0 ∈ Set.Ico (δ * (b : ℝ)) (δ * ((b : ℝ) + 1)) := h4 0
    have h6 : δ * (b : ℝ) ≤ p 0 := h5.1
    have h7 : p 0 < δ * ((b : ℝ) + 1) := h5.2
    have hp_eval' : p 0 = δ * (a : ℝ) := by exact hp_eval
    rw [hp_eval'] at h6 h7
    have h8 : (b : ℝ) ≤ (a : ℝ) := by
      have h_div : δ * (b : ℝ) / δ ≤ δ * (a : ℝ) / δ := by gcongr
      have h1 : δ * (b : ℝ) / δ = (b : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h2 : δ * (a : ℝ) / δ = (a : ℝ) := by field_simp [hδ.ne'] <;> ring
      rw [h1, h2] at h_div
      exact h_div
    have h9 : (a : ℝ) < (b : ℝ) + 1 := by
      have h_div : δ * (a : ℝ) / δ < δ * ((b : ℝ) + 1) / δ := by gcongr
      have h1 : δ * (a : ℝ) / δ = (a : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h2 : δ * ((b : ℝ) + 1) / δ = (b : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      rw [h1, h2] at h_div
      exact h_div
    have h10 : ⌊(a : ℝ)⌋ = b := by
      rw [Int.floor_eq_iff]
      exact ⟨h8, h9⟩
    have h11 : ⌊(a : ℝ)⌋ = a := by simp
    rw [h11] at h10
    exact h10

  have h_inj : Set.InjOn f S := by
    intro y hy z hz h_eq
    have h_k_eq : n' y = n' z := h_cube_inj (n' y) (n' z) h_eq
    have h_yy : y = δ * (n' y : ℝ) := h_y_eq y hy
    have h_zz : z = δ * (n' z : ℝ) := h_y_eq z hz
    rw [h_yy, h_zz, h_k_eq]

  have h_image_subset : f '' S ⊆ dyadicCubesMeeting δ (realLineCopy ((roundToDeltaGrid δ) ⁻¹' S)) := by
    intro Q hQ
    rcases hQ with ⟨y, hy, rfl⟩
    exact h_meets y hy
  have h_encard_eq : (f '' S).encard = S.encard := h_inj.encard_image
  have h_encard_le : (f '' S).encard ≤ (dyadicCubesMeeting δ (realLineCopy ((roundToDeltaGrid δ) ⁻¹' S))).encard :=
    Set.encard_mono h_image_subset
  have h_final : S.encard ≤ (dyadicCubesMeeting δ (realLineCopy ((roundToDeltaGrid δ) ⁻¹' S))).encard := by
    rw [←h_encard_eq]
    exact h_encard_le
  have h_goal : ENat.toENNReal S.encard ≤
      ENat.toENNReal (dyadicCubesMeeting δ (realLineCopy ((roundToDeltaGrid δ) ⁻¹' S))).encard := by
    exact ENat.toENNReal_le.mpr h_final
  simpa [Nreal, dyadicCoveringNumber] using h_goal

end robust_projection_main
