module

/-
# Frostman Measure from Delta-Set Property

Constructs a normalized counting Frostman measure on a grid subset Y from its
`(δ, τ, C)`-set property, with exponent `κ ≤ τ`.

## Main result

`frostman_from_delta_set`: normalized counting measure on Y satisfies
`IsDirectionFrostman δ κ C' μ` with `C' = 3 * C * 2^τ`.

## Proof sketch

1. For grid subsets, dyadic covering number equals cardinality.
2. Any interval of radius r can be covered by ≤ 3 dyadic cubes of scale q ∈ [r, 2r].
3. Sum the delta-set bounds over these cubes and use `κ ≤ τ`, `r ≤ 1`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.TauMonotonicity
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set Bornology ENNReal MeasureTheory Finset

namespace ProductLikeIncidence.ProductReduction

attribute [local instance] Classical.propDecidable

/-- Normalized counting measure on a finite nonempty set Y. -/
noncomputable def normalizedCountingMeasure (Y : Set ℝ) (hY_finite : Y.Finite) (hY_nonempty : Y.Nonempty) :
    Measure ℝ :=
  (ENat.toENNReal Y.encard)⁻¹ • Measure.count.restrict Y

/-- Helper: the half-open dyadic interval at scale q indexed by k. -/
def dyadicInterval (q : ℝ) (k : ℤ) : Set ℝ :=
  Set.Ico (q * (k : ℝ)) (q * ((k : ℝ) + 1))

/-- Existence of a dyadic scale q with r ≤ q < 2r, δ ≤ q ≤ 1. -/
lemma exists_dyadic_scale_between' {δ r : ℝ} (hδ : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales) (hr_pos : 0 < r) (hδ_le_r : δ ≤ r)
    (hr_le_one : r ≤ 1) :
    ∃ (q : ℝ), q ∈ dyadicScales ∧ δ ≤ q ∧ q ≤ 1 ∧ r ≤ q ∧ q < 2 * r := by
  have h_pow_ge : ∀ n : ℕ, (2 : ℝ)^n ≥ (n : ℝ) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases h : n = 0
      · subst h; norm_num
      · have h9 : (n : ℝ) ≥ 1 := by
          have h10 : n ≥ 1 := by omega
          exact_mod_cast h10
        calc (2 : ℝ)^(n + 1) = 2 * (2 : ℝ)^n := by ring
          _ ≥ 2 * (n : ℝ) := by gcongr
          _ ≥ (n : ℝ) + 1 := by linarith
          _ = ((n + 1 : ℕ) : ℝ) := by simp
  let P : ℕ → Prop := fun j => (2 : ℝ)^(-((j + 1 : ℕ) : ℝ)) < r
  have h_exists : ∃ j, P j := by
    have h2 : ∃ n : ℕ, (n : ℝ) > 1 / r := exists_nat_gt (1 / r)
    rcases h2 with ⟨n, hn⟩
    have h_n_ge2 : n ≥ 2 := by
      have h_r_le_one : 1 / r ≥ 1 := by
        have h1 : 0 < r := hr_pos
        have h2 : r ≤ 1 := hr_le_one
        exact one_le_one_div h1 h2
      have h3 : (n : ℝ) > 1 := by linarith
      by_contra h4
      have h5 : n ≤ 1 := by omega
      have h6 : (n : ℝ) ≤ 1 := by exact_mod_cast h5
      linarith
    have h3 : (2 : ℝ)^n ≥ (n : ℝ) := h_pow_ge n
    have h4 : (2 : ℝ)^n > 1 / r := by linarith
    refine ⟨n - 1, ?_⟩
    have h5 : n - 1 + 1 = n := by omega
    simp only [P, h5]
    have h6 : (2 : ℝ)^(-(n : ℝ)) < r := by
      have h7 : 0 < (2 : ℝ)^n := by positivity
      have h8 : 1 < (2 : ℝ)^n * r := by
        have h9 : 1 / r < (2 : ℝ)^n := h4
        have h10 : 0 < r := hr_pos
        calc 1 = (1 / r) * r := by field_simp [h10.ne'] <;> ring
          _ < (2 : ℝ)^n * r := by gcongr
      have h11 : (2 : ℝ)^(-(n : ℝ)) = 1 / (2 : ℝ)^(n : ℝ) := by
        rw [Real.rpow_neg (by norm_num)] <;> ring
      rw [h11]
      have h12 : (2 : ℝ)^(n : ℝ) = (2 : ℝ)^n := by simp
      rw [h12]
      have h13 : 0 < (2 : ℝ)^n := h7
      rw [one_div_lt h13] <;> nlinarith
    exact h6
  let j : ℕ := Nat.find h_exists
  have hj_prop : P j := Nat.find_spec h_exists
  have hj_min : ∀ i < j, ¬P i := fun i hi => Nat.find_min h_exists hi
  let q : ℝ := (2 : ℝ)^(-(j : ℝ))
  have hq_dyadic : q ∈ dyadicScales := ⟨j, by simp [q]⟩
  have hq_lt_2r : q < 2 * r := by
    simp only [q]
    have h1 : (2 : ℝ)^(-((j + 1 : ℕ) : ℝ)) < r := hj_prop
    have h2 : (2 : ℝ)^(-((j + 1 : ℕ) : ℝ)) = (2 : ℝ)^(-(j : ℝ)) / 2 := by
      have h3 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by simp
      rw [h3]
      have h41 : -((j : ℝ) + 1) = -(j : ℝ) + (-1 : ℝ) := by ring
      rw [h41]
      have h42 : (2 : ℝ)^(-(j : ℝ) + (-1 : ℝ)) = (2 : ℝ)^(-(j : ℝ)) * (2 : ℝ)^(-1 : ℝ) := by
        rw [Real.rpow_add (by norm_num)]
      rw [h42]
      have h5 : (2 : ℝ)^(-1 : ℝ) = 1 / 2 := by norm_num
      rw [h5] <;> ring
    rw [h2] at h1
    linarith
  have hq_ge_r : r ≤ q := by
    by_cases h_j : j = 0
    · have hq_eq : q = 1 := by
        simp [q, h_j]
      rw [hq_eq]
      exact hr_le_one
    · have h_j_pos : 0 < j := by omega
      have h5 : j - 1 < j := by omega
      have h6 : ¬P (j - 1) := hj_min (j - 1) h5
      simp only [P] at h6
      have h7 : (j - 1 + 1 : ℕ) = j := by omega
      have h7' : ((j - 1 + 1 : ℕ) : ℝ) = (j : ℝ) := by
        rw [h7]
      rw [h7'] at h6
      simpa [q] using h6
  have hq_le_one : q ≤ 1 := by
    simp [q]
    have h13 : (j : ℝ) ≥ 0 := by positivity
    have h14 : (2 : ℝ)^(-(j : ℝ)) ≤ (2 : ℝ)^(0 : ℝ) := by
      gcongr <;> linarith
    simpa using h14
  have hδ_le_q : δ ≤ q := by
    calc δ ≤ r := hδ_le_r
      _ ≤ q := hq_ge_r
  exact ⟨q, hq_dyadic, hδ_le_q, hq_le_one, hq_ge_r, hq_lt_2r⟩

/-- For a grid subset S, the dyadic covering number at scale δ equals the cardinality. -/
lemma grid_cover_eq_card {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS_grid : S ⊆ productLikeIntegerGrid δ) (hS_fin : S.Finite) :
    ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy S)) =
      ENat.toENNReal S.encard := by
  have h_bdd : Bornology.IsBounded S := hS_fin.isBounded
  have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy S) =
      (ProductLikeIncidence.realCubeIndexSet δ S).encard :=
    ProductLikeIncidence.realCoveringNumber_eq_card hδ h_bdd
  have h_idx_fin : (ProductLikeIncidence.realCubeIndexSet δ S).Finite :=
    ProductLikeIncidence.realCubeIndexSet_finite hδ h_bdd
  let f : ℤ → ℝ := fun k => δ * (k : ℝ)
  have h_mapsTo : Set.MapsTo f (ProductLikeIncidence.realCubeIndexSet δ S) S := by
    intro k hk
    simp only [ProductLikeIncidence.realCubeIndexSet, Set.mem_setOf_eq] at hk
    rcases hk with ⟨x, hx_in_cube, hxS⟩
    rcases hS_grid hxS with ⟨m, hm⟩
    have h5 : δ * (k : ℝ) ≤ δ * (m : ℝ) := by
      calc δ * (k : ℝ) ≤ x := hx_in_cube.1
        _ = δ * (m : ℝ) := hm
    have h6 : δ * (m : ℝ) < δ * ((k : ℝ) + 1) := by
      calc δ * (m : ℝ) = x := hm.symm
        _ < δ * ((k : ℝ) + 1) := hx_in_cube.2
    have h7 : (k : ℝ) ≤ (m : ℝ) := by
      have h_pos : 0 < δ := hδ
      nlinarith
    have h8 : (m : ℝ) < (k : ℝ) + 1 := by
      have h_pos : 0 < δ := hδ
      nlinarith
    have h7' : k ≤ m := by exact_mod_cast h7
    have h8' : m < k + 1 := by exact_mod_cast h8
    have h9 : m = k := by omega
    have h10 : δ * (k : ℝ) = x := by
      calc δ * (k : ℝ) = δ * (m : ℝ) := by rw [h9]
        _ = x := hm.symm
    have h_goal : f k = x := by
      simpa [f] using h10
    rw [h_goal]
    exact hxS
  have h_injOn : Set.InjOn f (ProductLikeIncidence.realCubeIndexSet δ S) := by
    intro k1 _ k2 _ h
    have h10 : (k1 : ℝ) = (k2 : ℝ) := by
      apply mul_left_cancel₀ hδ.ne'
      exact h
    exact_mod_cast h10
  have h_surjOn : Set.SurjOn f (ProductLikeIncidence.realCubeIndexSet δ S) S := by
    intro x hx
    rcases hS_grid hx with ⟨m, hm⟩
    have h5 : m ∈ ProductLikeIncidence.realCubeIndexSet δ S := by
      simp only [ProductLikeIncidence.realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨x, ?_, hx⟩
      constructor
      · rw [hm] <;> linarith
      · rw [hm] <;> linarith
    exact ⟨m, h5, by simp [f, hm]⟩
  have h2 : Set.BijOn f (ProductLikeIncidence.realCubeIndexSet δ S) S :=
    ⟨h_mapsTo, h_injOn, h_surjOn⟩
  have h_image : f '' (ProductLikeIncidence.realCubeIndexSet δ S) = S := h2.image_eq
  have h3 : (f '' (ProductLikeIncidence.realCubeIndexSet δ S)).encard =
      (ProductLikeIncidence.realCubeIndexSet δ S).encard := h_injOn.encard_image
  have h4 : (ProductLikeIncidence.realCubeIndexSet δ S).encard = S.encard := by
    rw [←h3, h_image]
  have h5 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy S)) =
      ENat.toENNReal (ProductLikeIncidence.realCubeIndexSet δ S).encard := by
    rw [h1]
  rw [h5, h4]

/-- A bounded subset of the δ-grid δℤ is finite. -/
lemma bounded_grid_subset_finite {δ : ℝ} (hδ : 0 < δ) {Y : Set ℝ}
    (hY_grid : Y ⊆ productLikeIntegerGrid δ) (hY_bdd : Bornology.IsBounded Y) :
    Y.Finite := by
  rcases Metric.isBounded_iff.mp hY_bdd with ⟨C0, hC0⟩
  have h1 : ∃ (M : ℝ), ∀ x ∈ Y, |x| ≤ M := by
    by_cases h : Y.Nonempty
    · rcases h with ⟨x0, hx0⟩
      refine ⟨C0 + |x0|, ?_⟩
      intro x hx
      have h2 : dist x x0 ≤ C0 := hC0 hx hx0
      have h3 : |x - x0| ≤ C0 := by
        rw [Real.dist_eq] at h2; exact h2
      have h4 : |x| ≤ |x - x0| + |x0| := by
        calc |x| = |(x - x0) + x0| := by ring_nf
          _ ≤ |x - x0| + |x0| := by exact abs_add_le (x - x0) x0
      linarith
    · exact ⟨0, fun x hx => False.elim (h ⟨x, hx⟩)⟩
  rcases h1 with ⟨M, hM⟩
  let k_min : ℤ := Int.ceil (-M / δ)
  let k_max : ℤ := Int.floor (M / δ)
  have h2 : Y ⊆ (fun k : ℤ => δ * (k : ℝ)) '' Finset.Icc k_min k_max := by
    intro x hx
    have h3 : |x| ≤ M := hM x hx
    have h4 : -M ≤ x := (abs_le.mp h3).1
    have h5 : x ≤ M := (abs_le.mp h3).2
    rcases hY_grid hx with ⟨k, hk⟩
    have h6 : -M ≤ δ * (k : ℝ) := by linarith [hk]
    have h7 : δ * (k : ℝ) ≤ M := by linarith [hk]
    have h9 : -M / δ ≤ (k : ℝ) := by
      have hdiv : -M / δ ≤ (δ * (k : ℝ)) / δ := by gcongr
      have hcancel : (δ * (k : ℝ)) / δ = (k : ℝ) := by
        field_simp [hδ.ne'] <;> ring
      rw [hcancel] at hdiv
      exact hdiv
    have h8 : k_min ≤ k := Int.ceil_le.mpr h9
    have h11 : (k : ℝ) ≤ M / δ := by
      have hdiv : (δ * (k : ℝ)) / δ ≤ M / δ := by gcongr
      have hcancel : (δ * (k : ℝ)) / δ = (k : ℝ) := by
        field_simp [hδ.ne'] <;> ring
      rw [hcancel] at hdiv
      exact hdiv
    have h10 : k ≤ k_max := Int.le_floor.mpr h11
    have h12 : k ∈ Finset.Icc k_min k_max := by
      simp only [Finset.mem_Icc]
      exact ⟨h8, h10⟩
    exact ⟨k, h12, hk.symm⟩
  have h3 : Set.Finite ((fun k : ℤ => δ * (k : ℝ)) '' Finset.Icc k_min k_max) :=
    Set.Finite.image _ (Finset.finite_toSet _)
  exact Set.Finite.subset h3 h2

/-- Core Frostman construction from a bounded (δ,τ,C)-grid set Y.
Outputs normalized counting measure μ with μ.support = Y and the Frostman
ball condition. Does NOT require Y ⊆ [0,1]. -/
lemma frostman_from_bounded_delta_set {δ τ κ C : ℝ} {Y : Set ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hκ_le_tau : κ ≤ τ)
    (hC_pos : 0 < C)
    (hY_grid : Y ⊆ productLikeIntegerGrid δ)
    (hY_bdd : Bornology.IsBounded Y)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y) :
    ∃ (μ : Measure ℝ),
      (μ Set.univ = 1) ∧
      (∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
        μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal ((3 * C * 2 ^ τ) * r ^ κ)) ∧
      (μ.support = Y) ∧
      (∀ y ∈ Y, μ {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))) := by
  have hY_finite : Y.Finite := bounded_grid_subset_finite hδ hY_grid hY_bdd
  have hY_nonempty_eucl : (productLikeRealLineCopy Y).Nonempty := hY_delta.2.1
  have hY_nonempty : Y.Nonempty := by
    rcases hY_nonempty_eucl with ⟨x, hx⟩
    exact ⟨x 0, hx⟩
  let μ : Measure ℝ := normalizedCountingMeasure Y hY_finite hY_nonempty
  let c_enn : ENNReal := (ENat.toENNReal Y.encard)⁻¹
  have hc_pos : 0 < ENat.toENNReal Y.encard := by
    have h : 0 < Y.encard := Set.encard_pos.mpr hY_nonempty
    exact_mod_cast h
  have hY_encard_lt_top : Y.encard < ⊤ := hY_finite.encard_lt_top
  have hY_encard_ne_top : ENat.toENNReal Y.encard ≠ ⊤ := by
    exact_mod_cast hY_encard_lt_top.ne
  have hτ_pos : 0 < τ := by linarith
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · -- μ Set.univ = 1
    have h_count : (Measure.count.restrict Y) Set.univ = ENat.toENNReal Y.encard := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
      exact MeasureTheory.Measure.count_apply hY_finite.measurableSet
    have h1 : μ Set.univ = c_enn * ENat.toENNReal Y.encard := by
      simp [μ, normalizedCountingMeasure, h_count] <;> ring
    rw [h1]
    exact ENNReal.inv_mul_cancel (ne_of_gt hc_pos) hY_encard_ne_top
  · -- Frostman ball condition
    intro a r hδ_le_r hr_le_one
    rcases exists_dyadic_scale_between' hδ hδ_dyadic (by linarith) hδ_le_r hr_le_one
      with ⟨q, hq_dyadic, hδ_le_q, hq_le_one, hq_ge_r, hq_lt_2r⟩
    set k0 : ℤ := Int.floor ((a - r) / q) with hk0
    let R : ℤ → Set ℝ := dyadicInterval q
    let R0 : Set ℝ := Set.Ico (q * (k0 : ℝ)) (q * ((k0 : ℝ) + 1))
    let R1 : Set ℝ := Set.Ico (q * ((k0 : ℝ) + 1)) (q * ((k0 : ℝ) + 2))
    let R2 : Set ℝ := Set.Ico (q * ((k0 : ℝ) + 2)) (q * ((k0 : ℝ) + 3))
    have hR0 : R0 = R k0 := by
      congr <;> simp [R0, R, dyadicInterval] <;> ring
    have hR1 : R1 = R (k0 + 1) := by
      congr <;> simp [R1, R, dyadicInterval, Int.cast_add] <;> ring_nf
    have hR2 : R2 = R (k0 + 2) := by
      congr <;> simp [R2, R, dyadicInterval, Int.cast_add] <;> ring_nf
    set Q : ℤ → Set (EuclideanSpace ℝ (Fin 1)) :=
      fun k => dyadicCube q (fun (_ : Fin 1) => k) with hQ
    have hq_pos : 0 < q := by linarith
    have h1 : q * (k0 : ℝ) ≤ a - r := by
      have h : (k0 : ℝ) ≤ (a - r) / q := Int.floor_le ((a - r) / q)
      have hq_pos' : 0 < q := hq_pos
      calc q * (k0 : ℝ) ≤ q * ((a - r) / q) := by gcongr
        _ = a - r := by field_simp [hq_pos'.ne'] <;> ring
    have h2 : a - r < q * ((k0 : ℝ) + 1) := by
      have h : (a - r) / q < (k0 : ℝ) + 1 := Int.lt_floor_add_one ((a - r) / q)
      have hq_pos' : 0 < q := hq_pos
      calc a - r = q * ((a - r) / q) := by field_simp [hq_pos'.ne'] <;> ring
        _ < q * (((k0 : ℝ) + 1)) := by gcongr
    have h3 : a + r < q * ((k0 : ℝ) + 3) := by
      have h4 : 2 * r ≤ 2 * q := by gcongr
      calc a + r = (a - r) + 2 * r := by ring
        _ < q * ((k0 : ℝ) + 1) + 2 * r := by gcongr
        _ ≤ q * ((k0 : ℝ) + 1) + 2 * q := by gcongr
        _ = q * ((k0 : ℝ) + 3) := by ring
    set I : Set ℝ := Set.Icc (a - r) (a + r) with hI
    have h_cover : I ⊆ R k0 ∪ R (k0 + 1) ∪ R (k0 + 2) := by
      intro x hx
      have h_x_ge : q * (k0 : ℝ) ≤ x := by linarith [hx.1, h1]
      have h_x_lt : x < q * ((k0 : ℝ) + 3) := by linarith [hx.2, h3]
      by_cases h5 : x < q * ((k0 : ℝ) + 1)
      · have h_goal : x ∈ R0 := ⟨h_x_ge, h5⟩
        rw [hR0] at h_goal
        exact Set.mem_union_left (R (k0 + 2)) (Set.mem_union_left (R (k0 + 1)) h_goal)
      · have h5' : q * ((k0 : ℝ) + 1) ≤ x := by linarith
        by_cases h6 : x < q * ((k0 : ℝ) + 2)
        · have h_goal : x ∈ R1 := ⟨h5', h6⟩
          rw [hR1] at h_goal
          exact Set.mem_union_left (R (k0 + 2)) (Set.mem_union_right (R k0) h_goal)
        · have h6' : q * ((k0 : ℝ) + 2) ≤ x := by linarith
          have h_goal : x ∈ R2 := ⟨h6', h_x_lt⟩
          rw [hR2] at h_goal
          exact Set.mem_union_right (R k0 ∪ R (k0 + 1)) h_goal
    have hY_inter_cover : Y ∩ I ⊆ (Y ∩ R k0) ∪ (Y ∩ R (k0 + 1)) ∪ (Y ∩ R (k0 + 2)) := by
      intro x hx
      have hxY : x ∈ Y := hx.1
      have hxI : x ∈ I := hx.2
      have h4 : x ∈ R k0 ∪ R (k0 + 1) ∪ R (k0 + 2) := h_cover hxI
      cases' h4 with h4 h4
      · cases' h4 with h4' h4'
        · have h_goal : x ∈ Y ∩ R k0 := ⟨hxY, h4'⟩
          exact Set.mem_union_left (Y ∩ R (k0 + 2)) (Set.mem_union_left (Y ∩ R (k0 + 1)) h_goal)
        · have h_goal : x ∈ Y ∩ R (k0 + 1) := ⟨hxY, h4'⟩
          exact Set.mem_union_left (Y ∩ R (k0 + 2)) (Set.mem_union_right (Y ∩ R k0) h_goal)
      · have h_goal : x ∈ Y ∩ R (k0 + 2) := ⟨hxY, h4⟩
        exact Set.mem_union_right ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))) h_goal
    have h_main_bound : ∀ (k : ℤ),
        ENat.toENNReal (Y ∩ R k).encard ≤
          ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ) := by
      intro k
      have hQ_in : Q k ∈ dyadicCubes 1 q := by
        simp only [dyadicCubes, Set.mem_setOf_eq, hQ]
        exact ⟨(fun (_ : Fin 1) => k), rfl⟩
      have h_eq1 : productLikeRealLineCopy Y ∩ Q k = productLikeRealLineCopy (Y ∩ R k) := by
        ext x
        simp [productLikeRealLineCopy, hQ, R, dyadicInterval, dyadicCube, Set.mem_inter_iff, Set.mem_Ico]
        <;> constructor <;> intro h <;> simp_all [Set.mem_Ico] <;> tauto
      have h_delta := hY_delta.2.2.2.2.2.2.2.2 hq_dyadic hQ_in hδ_le_q hq_le_one
      have h_sub1 : Y ∩ R k ⊆ Y := by intro z hz; exact hz.1
      have h_card1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y ∩ Q k)) =
          ENat.toENNReal (Y ∩ R k).encard := by
        rw [h_eq1]
        exact grid_cover_eq_card hδ (Subset.trans h_sub1 hY_grid) (hY_finite.subset h_sub1)
      have h_cardY : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y)) =
          ENat.toENNReal Y.encard := grid_cover_eq_card hδ hY_grid hY_finite
      rw [h_card1, h_cardY] at h_delta
      exact h_delta
    have h_sum_bound : ENat.toENNReal (Y ∩ I).encard ≤
        ENat.toENNReal (Y ∩ R k0).encard +
        ENat.toENNReal (Y ∩ R (k0 + 1)).encard +
        ENat.toENNReal (Y ∩ R (k0 + 2)).encard := by
      have h_encard_le : ENat.toENNReal (Y ∩ I).encard ≤
          ENat.toENNReal ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1)) ∪ (Y ∩ R (k0 + 2))).encard := by
        exact_mod_cast Set.encard_mono hY_inter_cover
      have h_union1 : ENat.toENNReal ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))).encard ≤
          ENat.toENNReal (Y ∩ R k0).encard + ENat.toENNReal (Y ∩ R (k0 + 1)).encard := by
        exact_mod_cast Set.encard_union_le _ _
      have h_union2 : ENat.toENNReal (((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))) ∪ (Y ∩ R (k0 + 2))).encard ≤
          ENat.toENNReal ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))).encard + ENat.toENNReal (Y ∩ R (k0 + 2)).encard := by
        exact_mod_cast Set.encard_union_le _ _
      calc ENat.toENNReal (Y ∩ I).encard
        ≤ ENat.toENNReal ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1)) ∪ (Y ∩ R (k0 + 2))).encard := h_encard_le
        _ = ENat.toENNReal (((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))) ∪ (Y ∩ R (k0 + 2))).encard := by rfl
        _ ≤ ENat.toENNReal ((Y ∩ R k0) ∪ (Y ∩ R (k0 + 1))).encard + ENat.toENNReal (Y ∩ R (k0 + 2)).encard := h_union2
        _ ≤ (ENat.toENNReal (Y ∩ R k0).encard + ENat.toENNReal (Y ∩ R (k0 + 1)).encard) + ENat.toENNReal (Y ∩ R (k0 + 2)).encard := by gcongr
        _ = ENat.toENNReal (Y ∩ R k0).encard + ENat.toENNReal (Y ∩ R (k0 + 1)).encard + ENat.toENNReal (Y ∩ R (k0 + 2)).encard := by ring
    have h_each : ∀ (k : ℤ), ENat.toENNReal (Y ∩ R k).encard ≤
        ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ) := h_main_bound
    have h4 : ENat.toENNReal (Y ∩ I).encard ≤
        3 * (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) := by
      calc ENat.toENNReal (Y ∩ I).encard
        ≤ ENat.toENNReal (Y ∩ R k0).encard +
            ENat.toENNReal (Y ∩ R (k0 + 1)).encard +
            ENat.toENNReal (Y ∩ R (k0 + 2)).encard := h_sum_bound
        _ ≤ (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) +
            (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) +
            (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) := by
          gcongr <;> exact h_each _
        _ = 3 * (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) := by ring
    have hq_pow_le : q ^ τ ≤ (2 * r) ^ τ := by gcongr <;> linarith
    have h5 : (2 * r) ^ τ = (2 : ℝ) ^ τ * r ^ τ := by
      rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    have h_rpow_le : r ^ τ ≤ r ^ κ := by
      apply Real.rpow_le_rpow_of_exponent_le_or_ge
      exact Or.inr ⟨by linarith, hr_le_one, hκ_le_tau⟩
    have h6 : q ^ τ ≤ (2 : ℝ) ^ τ * r ^ κ := by
      calc q ^ τ ≤ (2 * r) ^ τ := hq_pow_le
        _ = (2 : ℝ) ^ τ * r ^ τ := h5
        _ ≤ (2 : ℝ) ^ τ * r ^ κ := by gcongr
    have h7 : ENNReal.ofReal (q ^ τ) ≤ ENNReal.ofReal ((2 : ℝ) ^ τ * r ^ κ) := by
      exact ENNReal.ofReal_le_ofReal h6
    have hr_pos : 0 < r := by linarith [hδ_le_r]
    have h_pos1 : 0 ≤ (2 : ℝ) ^ τ := by positivity
    have h_pos2 : 0 ≤ r ^ κ := by positivity
    have h_pos3 : 0 ≤ C := by linarith
    have h_eq : ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) =
        3 * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ τ) * ENNReal.ofReal (r ^ κ) := by
      have h91 : 0 ≤ 3 * C := by linarith
      have h92 : 0 ≤ (3 * C) * (2 : ℝ) ^ τ := by positivity
      have h1 : ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) =
          ENNReal.ofReal ((3 * C) * (2 : ℝ) ^ τ) * ENNReal.ofReal (r ^ κ) := by
        rw [ENNReal.ofReal_mul h92]
      have h2 : ENNReal.ofReal ((3 * C) * (2 : ℝ) ^ τ) =
          ENNReal.ofReal (3 * C) * ENNReal.ofReal ((2 : ℝ) ^ τ) := by
        rw [ENNReal.ofReal_mul h91]
      have h3 : ENNReal.ofReal (3 * C) = 3 * ENNReal.ofReal C := by
        have h4 : ENNReal.ofReal (3 * C) = ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul (by linarith)]
        rw [h4] <;> norm_num
      rw [h1, h2, h3] <;> ring
    have h8 : 3 * (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ)) ≤
        ENat.toENNReal Y.encard * ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) := by
      calc 3 * (ENNReal.ofReal C * ENat.toENNReal Y.encard * ENNReal.ofReal (q ^ τ))
        = ENat.toENNReal Y.encard * (3 * ENNReal.ofReal C * ENNReal.ofReal (q ^ τ)) := by ring
        _ ≤ ENat.toENNReal Y.encard * (3 * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ τ * r ^ κ)) := by gcongr
        _ = ENat.toENNReal Y.encard * (3 * ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ τ) * ENNReal.ofReal (r ^ κ)) := by
          have h5 : ENNReal.ofReal ((2 : ℝ) ^ τ * r ^ κ) =
              ENNReal.ofReal ((2 : ℝ) ^ τ) * ENNReal.ofReal (r ^ κ) := by
            rw [ENNReal.ofReal_mul h_pos1]
          rw [h5] <;> ring
        _ = ENat.toENNReal Y.encard * ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) := by
          rw [h_eq] <;> ring
    have h9 : ENat.toENNReal (Y ∩ I).encard ≤
        ENat.toENNReal Y.encard * ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) :=
      le_trans h4 h8
    have hI_meas : MeasurableSet I := measurableSet_Icc
    have h_sub : Y ∩ I ⊆ Y := by intro z hz; exact hz.1
    have h_YI_fin : (Y ∩ I).Finite := hY_finite.subset h_sub
    have h_count1 := MeasureTheory.Measure.count_apply h_YI_fin.measurableSet
    have h_count : (Measure.count.restrict Y) I = ENat.toENNReal (Y ∩ I).encard := by
      rw [Measure.restrict_apply hI_meas]
      have h_comm : I ∩ Y = Y ∩ I := Set.inter_comm I Y
      rw [h_comm]
      simpa using h_count1
    have h10 : μ I = c_enn * ENat.toENNReal (Y ∩ I).encard := by
      simp [μ, normalizedCountingMeasure, h_count] <;> ring
    rw [h10]
    have h11 : c_enn * ENat.toENNReal (Y ∩ I).encard ≤
        c_enn * (ENat.toENNReal Y.encard * ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ)) := by gcongr
    have h12 : c_enn * ENat.toENNReal Y.encard = 1 :=
      ENNReal.inv_mul_cancel (ne_of_gt hc_pos) hY_encard_ne_top
    have h13 : c_enn * (ENat.toENNReal Y.encard * ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ)) =
        ENNReal.ofReal (3 * C * (2 : ℝ) ^ τ * r ^ κ) := by
      rw [←mul_assoc, h12, one_mul]
    rw [h13] at h11
    exact h11
  · -- μ.support = Y
    have hY_closed : IsClosed Y := hY_finite.isClosed
    have h_count_compl : (Measure.count.restrict Y) Yᶜ = 0 := by
      rw [Measure.restrict_apply hY_closed.isOpen_compl.measurableSet]
      <;> simp [Set.inter_compl_self]
    have h_compl : μ Yᶜ = 0 := by
      simp [μ, normalizedCountingMeasure, h_count_compl]
    have h_supp_sub_Y : μ.support ⊆ Y :=
      MeasureTheory.Measure.support_subset_of_isClosed hY_closed h_compl
    have h_Y_sub_supp : Y ⊆ μ.support := by
      intro y hy
      have h3 : μ {y} = c_enn := by
        simp [μ, normalizedCountingMeasure, Measure.count_apply, hY_finite, hy] <;> ring
      have h_pos : 0 < μ {y} := by
        rw [h3]
        exact ENNReal.inv_pos.mpr hY_encard_ne_top
      have h_main : y ∈ μ.support := by
        by_contra h
        have h5 : μ {y} = 0 := by
          have h6 : {y} ⊆ (μ.support)ᶜ := by
            intro z hz
            have hz' : z = y := by simpa using hz
            rw [hz']
            exact h
          have h7 : μ {y} ≤ μ ((μ.support)ᶜ) := measure_mono h6
          have h8 : μ ((μ.support)ᶜ) = 0 := μ.measure_compl_support
          exact le_zero_iff.mp (le_trans h7 h8.le)
        rw [h5] at h_pos
        <;> simpa using h_pos
      exact h_main
    exact Set.Subset.antisymm h_supp_sub_Y h_Y_sub_supp
  · -- ∀ y ∈ Y, μ {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))
    intro y hy
    have h3 : μ {y} = c_enn := by
      simp [μ, normalizedCountingMeasure, Measure.count_apply, hY_finite, hy] <;> ring
    rw [h3]
    let Yf : Finset ℝ := hY_finite.toFinset
    have hYf_eq : (Yf : Set ℝ) = Y := Set.Finite.coe_toFinset hY_finite
    have hYf_nonempty : Yf.Nonempty := by
      rcases hY_nonempty with ⟨y', hy'⟩
      have h_in : y' ∈ (Yf : Set ℝ) := by
        have h : (Yf : Set ℝ) = Y := hYf_eq
        rw [h]
        exact hy'
      exact ⟨y', h_in⟩
    have h_ncard_pos : 0 < Y.ncard := by
      have h_eq : (Yf : Set ℝ) = Y := hYf_eq
      have h : Y.ncard = Yf.card := by
        have h' : Y.ncard = ((Yf : Set ℝ)).ncard := by rw [h_eq]
        rw [h']; simp
      rw [h]; exact Finset.card_pos.mpr hYf_nonempty
    have h_pos' : (0 : ℝ) < (Y.ncard : ℝ) := by exact_mod_cast h_ncard_pos
    have h_mul : ENNReal.ofReal (1 / (Y.ncard : ℝ)) * (↑Y.ncard : ENNReal) = 1 := by
      have h9 : (↑Y.ncard : ENNReal) = ENNReal.ofReal (Y.ncard : ℝ) := by norm_cast
      rw [h9, ← ENNReal.ofReal_mul (by positivity)]
      have h10 : (1 / (Y.ncard : ℝ)) * (Y.ncard : ℝ) = 1 := by
        field_simp [h_pos'.ne'] <;> ring
      rw [h10]; simp
    have h_ne_zero : (↑Y.ncard : ENNReal) ≠ 0 := by exact_mod_cast h_ncard_pos.ne'
    have h_ne_top : (↑Y.ncard : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h4 : ENat.toENNReal Y.encard = (↑Y.ncard : ENNReal) := by
      have h5 : Y.encard = ↑Y.ncard := Set.Finite.encard_eq_coe hY_finite
      rw [h5] <;> simp
    have h6 : c_enn = (↑Y.ncard : ENNReal)⁻¹ := by
      simp [c_enn, h4] <;> rfl
    rw [h6]
    apply (ENNReal.mul_left_inj h_ne_zero h_ne_top).mp
    rw [h_mul, ENNReal.inv_mul_cancel h_ne_zero h_ne_top]

/-- From a (δ,τ,C)-set Y ⊆ δℤ ∩ [0,1], construct a direction Frostman measure
with exponent κ ≤ τ and constant 3 * C * 2^τ. Also returns that the measure
is the normalized counting measure on Y. -/
lemma frostman_from_delta_set {δ τ κ C : ℝ} {Y : Set ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hκ_le_tau : κ ≤ τ)
    (hC_pos : 0 < C)
    (hY_grid : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y) :
    ∃ (μ : Measure ℝ),
      IsDirectionFrostman δ κ (3 * C * 2 ^ τ) μ ∧
      μ.support = Y ∧
      (∀ y ∈ Y, μ {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))) := by
  have hY_grid' : Y ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact (hY_grid hx).1
  have hY_sub_Icc : Y ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx; exact (hY_grid hx).2
  have hY_bdd : Bornology.IsBounded Y :=
    IsBounded.subset (Metric.isBounded_Icc 0 1) hY_sub_Icc
  rcases frostman_from_bounded_delta_set hδ hδ_dyadic hδ_le_one hκ_pos hκ_le_tau hC_pos
      hY_grid' hY_bdd hY_delta
    with ⟨μ, hμ_univ, hμ_frost, hμ_supp, hμ_point⟩
  have h_supp_sub_Icc : μ.support ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [hμ_supp]
    exact hY_sub_Icc
  have h_dir_frost : IsDirectionFrostman δ κ (3 * C * 2 ^ τ) μ :=
    ⟨hμ_univ, h_supp_sub_Icc, hμ_frost⟩
  exact ⟨μ, h_dir_frost, hμ_supp, hμ_point⟩

end ProductLikeIncidence.ProductReduction
