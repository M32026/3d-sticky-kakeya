import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperBroadMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper

/-!
# Weak planiness wiring for Pure WZ2 grains

Chains the multilinear Kakeya estimate → broad mass budget → narrow pruning →
weak planiness to produce a plane map with incidence `tau / kappa`.

This is Step 1 of the multiscale pipeline. The absorption condition, multiplicity
condition, and close-direction count are taken as hypotheses while their proofs
are being developed separately.

## Chain

1. CV estimate (provided as `hCV` for a specific constant `C`)
2. `paper_broad_mass_budget_main` → broad set mass bound (needs absorption)
3. `paper_narrow_pruning` → narrow refinement data
4. `paper_weak_planiness_from_narrow` → weak plane map incidence `tau / kappa`

## Hypotheses to be filled in

- `h_absorb`: absorption condition for the specific CV constant `C`
- `hmult`: multiplicity growth condition for weak planiness
- `hclose`: close-direction count bound (use `pureWz2_close_direction_count_general`
  from `LocalAD.lean`; not imported here to avoid duplicate `PaperIsSubshading`)

## Note

The CV constant `C` and its estimate `hCV` are taken as explicit parameters rather
than obtained from `paper_cv_broad_set_estimate` inside the theorem. This avoids
requiring the absorption condition to hold for *all* finite `C`, which would be
mathematically impossible (LHS grows with C while RHS is fixed).
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Multiplicity growth condition for weak planiness.

With `Q = 1`, for any natural `μ ≥ 4*R + 2`, we have
`4 * (1 + 3 * R * μ^2) ≤ 3 * μ^3`.

Proof: `3μ³ - 12Rμ² - 4 = 3μ²(μ - 4R) - 4 ≥ 3μ²·2 - 4 ≥ 3·4·2 - 4 > 0`. -/
lemma weak_planiness_hmult (R : ℕ) (μ : ℕ) (h : 4 * R + 2 ≤ μ) :
    4 * (1 + 3 * R * μ ^ 2) ≤ 3 * μ ^ 3 := by
  have h_real : (4 : ℝ) * (1 + 3 * (R : ℝ) * (μ : ℝ)^2) ≤ 3 * (μ : ℝ)^3 := by
    have h1 : (4 : ℝ) * (R : ℝ) + 2 ≤ (μ : ℝ) := by exact_mod_cast h
    have h2 : (μ : ℝ) - 4 * (R : ℝ) ≥ 2 := by linarith
    have h3 : 0 ≤ (μ : ℝ) := by linarith
    have h4 : (μ : ℝ) ≥ 2 := by linarith
    nlinarith [sq_nonneg ((μ : ℝ)), sq_nonneg ((μ : ℝ) - 4 * (R : ℝ))]
  exact_mod_cast h_real

/--
Step 1 wiring: extremal configuration + hypotheses → weak plane map.

Given a cropped extremal configuration, plus the absorption, multiplicity, and
close-direction conditions, produce a selected subshading with a weak plane map
of incidence `tau / kappa`.

The critical hypothesis `h_absorb` is being proved separately using the balanced
cover multiplicity uniformity. The `hclose` bound can be discharged using
`pureWz2_close_direction_count_general` from `LocalAD.lean`.
-/
theorem weak_planiness_wiring
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hF_nonempty : F.Nonempty)
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ paperShadingTrilinearMultiplicity S p ^ (1 / 2 : ℝ)) →
          L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (Q R : ℕ)
    (tau kappa M : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    (hkappa_pos : 0 < kappa)
    (hM_pos : 0 < M)
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) ≤ ENNReal.ofReal M)
    -- Absorption condition for this specific C
    (h_absorb :
      (2 : ENNReal) * ENNReal.ofReal M * C *
        (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * S.mass)
    -- Multiplicity growth condition (placeholder)
    (hmult : ∀ p ∈ S.union,
      let mu := S.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3)
    -- Close direction count bound (use pureWz2_close_direction_count_general)
    (hclose : ∀ p ∈ S.union, ∀ i,
      p ∈ S.carrier i → paperCloseDirectionCount S p i kappa < R) :
    ∃ (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa)),
      PaperIsSubshading selected S ∧
      (1 / 8 : ENNReal) * S.mass ≤ selected.mass := by
  -- Step 1: Use provided CV constant and estimate
  have hC : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ paperShadingTrilinearMultiplicity S p ^ (1 / 2 : ℝ)) →
          L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) := by
    intro E hE _ L hL
    exact hCV E hE (by tauto) L hL

  -- Step 2: Broad mass budget
  let M_enn : ENNReal := ENNReal.ofReal M
  have hbroad_small : 2 * (∫⁻ p in paperCountedBroadSet S tau Q,
        (S.pointMultiplicity p : ENNReal)) ≤ S.mass :=
    paper_broad_mass_budget_main
      C hC M_enn hmult_upper Q tau hQ_pos htau_pos h_absorb

  -- Step 3: Narrow pruning
  have hB_meas : MeasurableSet (paperCountedBroadSet S tau Q) :=
    paperCountedBroadSet_measurable S tau Q
  have h_narrow : Nonempty (PaperWZ1NarrowRefinementData S tau Q) :=
    paper_narrow_pruning hB_meas hbroad_small
  rcases h_narrow with ⟨narrow⟩

  -- Step 4: Transfer close-direction bound to narrow subshading
  have hclose_narrow : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R := by
    intro p hp i hi
    have h_sub_i : narrow.shading.carrier i ⊆ S.carrier i := narrow.subshading i
    have h_p_in_S : p ∈ S.union := by
      exact ⟨i, h_sub_i hi⟩
    have h1 : paperCloseDirectionCount narrow.shading p i kappa ≤
             paperCloseDirectionCount S p i kappa := by
      apply Finset.card_le_card
      intro j hj
      have h2 := (Finset.mem_filter.mp hj).2
      have h_sub_j : narrow.shading.carrier j ⊆ S.carrier j := narrow.subshading j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨h_sub_j h2.1, h2.2⟩⟩
    have h4 : paperCloseDirectionCount S p i kappa < R :=
      hclose p h_p_in_S i (h_sub_i hi)
    exact lt_of_le_of_lt h1 h4

  -- Step 5: Transfer multiplicity condition to narrow subshading.
  -- For p in narrow.shading.union, p is not in the broad set, so every carrier
  -- membership is preserved: narrow.shading.carrier j = S.carrier j \\ broadSet
  -- and p ∉ broadSet implies p ∈ narrow.shading.carrier j ↔ p ∈ S.carrier j.
  have hmult_narrow : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    have hcarrier_i : narrow.shading.carrier i = S.carrier i \ paperCountedBroadSet S tau Q :=
      narrow.carrier_eq i
    have h_not_broad : p ∉ paperCountedBroadSet S tau Q := by
      rw [hcarrier_i] at hi
      exact hi.2
    have h_mult_eq : narrow.shading.pointMultiplicity p = S.pointMultiplicity p := by
      classical
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hcarrier_j : narrow.shading.carrier j = S.carrier j \ paperCountedBroadSet S tau Q :=
        narrow.carrier_eq j
      constructor
      · intro h
        rw [hcarrier_j] at h
        exact h.1
      · intro h
        rw [hcarrier_j]
        exact ⟨h, h_not_broad⟩
    rw [h_mult_eq]
    have h_p_in_S : p ∈ S.union := ⟨i, (narrow.subshading i) hi⟩
    exact hmult p h_p_in_S

  -- Step 6: Weak planiness
  have h_main := paper_weak_planiness_from_narrow
    hkappa_pos hF_nonempty narrow hclose_narrow hmult_narrow

  rcases h_main with ⟨selection, selected, planeMap, h_sub_selected, h_mass⟩
  have h_sub_S : PaperIsSubshading selected S := by
    intro i
    exact Set.Subset.trans (h_sub_selected i) (narrow.subshading i)
  have h_mass_total : (1 / 8 : ENNReal) * S.mass ≤ selected.mass := by
    have hmass1 : (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := h_mass
    have hmass2 : (1 / 2 : ENNReal) * S.mass ≤ narrow.shading.mass := narrow.mass_lower
    have h_coeff : (1 / 4 : ENNReal) * (1 / 2 : ENNReal) = (1 / 8 : ENNReal) := by
      simp only [one_div]
      have hmul : (4 : ENNReal) * (2 : ENNReal) = (8 : ENNReal) := by norm_num
      have hinv : ((4 : ENNReal) * (2 : ENNReal))⁻¹ = (4 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
        rw [ENNReal.mul_inv] <;> simp
      rw [hmul] at hinv
      exact hinv.symm
    calc
      (1 / 8 : ENNReal) * S.mass
        = ((1 / 4 : ENNReal) * (1 / 2 : ENNReal)) * S.mass := by rw [h_coeff]
      _ = (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) := by rw [mul_assoc]
      _ ≤ (1 / 4 : ENNReal) * narrow.shading.mass := by
        exact mul_le_mul_of_nonneg_left hmass2 (by positivity)
      _ ≤ selected.mass := hmass1
  exact ⟨selected, planeMap, h_sub_S, h_mass_total⟩

/-- Conditional variant of `weak_planiness_wiring`.

Only requires the multiplicity growth condition on points that are NOT in
the counted broad set. This is the mathematically natural statement, since
the broad set is pruned before the growth condition is used. -/
theorem weak_planiness_wiring_conditional
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hF_nonempty : F.Nonempty)
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ paperShadingTrilinearMultiplicity S p ^ (1 / 2 : ℝ)) →
          L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (Q R : ℕ)
    (tau kappa M : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    (hkappa_pos : 0 < kappa)
    (hM_pos : 0 < M)
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) ≤ ENNReal.ofReal M)
    (h_absorb :
      (2 : ENNReal) * ENNReal.ofReal M * C *
        (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau) ^ (1 / 2 : ℝ)) * S.mass)
    (hmult_conditional : ∀ p ∈ S.union, p ∉ paperCountedBroadSet S tau Q →
      let mu := S.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3)
    (hclose : ∀ p ∈ S.union, ∀ i,
      p ∈ S.carrier i → paperCloseDirectionCount S p i kappa < R) :
    ∃ (selected : WZ1PaperTubeShading F)
      (planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa)),
      PaperIsSubshading selected S ∧
      (1 / 8 : ENNReal) * S.mass ≤ selected.mass := by
  have hC : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ paperShadingTrilinearMultiplicity S p ^ (1 / 2 : ℝ)) →
          L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ) := by
    intro E hE _ L hL
    exact hCV E hE (by tauto) L hL
  let M_enn : ENNReal := ENNReal.ofReal M
  have hbroad_small : 2 * (∫⁻ p in paperCountedBroadSet S tau Q,
        (S.pointMultiplicity p : ENNReal)) ≤ S.mass :=
    paper_broad_mass_budget_main
      C hC M_enn hmult_upper Q tau hQ_pos htau_pos h_absorb
  have hB_meas : MeasurableSet (paperCountedBroadSet S tau Q) :=
    paperCountedBroadSet_measurable S tau Q
  have h_narrow : Nonempty (PaperWZ1NarrowRefinementData S tau Q) :=
    paper_narrow_pruning hB_meas hbroad_small
  rcases h_narrow with ⟨narrow⟩
  have hclose_narrow : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R := by
    intro p hp i hi
    have h_sub_i : narrow.shading.carrier i ⊆ S.carrier i := narrow.subshading i
    have h_p_in_S : p ∈ S.union := ⟨i, h_sub_i hi⟩
    have h1 : paperCloseDirectionCount narrow.shading p i kappa ≤
             paperCloseDirectionCount S p i kappa := by
      apply Finset.card_le_card
      intro j hj
      have h2 := (Finset.mem_filter.mp hj).2
      have h_sub_j : narrow.shading.carrier j ⊆ S.carrier j := narrow.subshading j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨h_sub_j h2.1, h2.2⟩⟩
    have h4 : paperCloseDirectionCount S p i kappa < R :=
      hclose p h_p_in_S i (h_sub_i hi)
    exact lt_of_le_of_lt h1 h4
  have hmult_narrow : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    have hcarrier_i : narrow.shading.carrier i = S.carrier i \ paperCountedBroadSet S tau Q :=
      narrow.carrier_eq i
    have h_not_broad : p ∉ paperCountedBroadSet S tau Q := by
      rw [hcarrier_i] at hi; exact hi.2
    have h_mult_eq : narrow.shading.pointMultiplicity p = S.pointMultiplicity p := by
      classical
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hcarrier_j : narrow.shading.carrier j = S.carrier j \ paperCountedBroadSet S tau Q :=
        narrow.carrier_eq j
      constructor
      · intro h; rw [hcarrier_j] at h; exact h.1
      · intro h; rw [hcarrier_j]; exact ⟨h, h_not_broad⟩
    rw [h_mult_eq]
    have h_p_in_S : p ∈ S.union := ⟨i, (narrow.subshading i) hi⟩
    exact hmult_conditional p h_p_in_S h_not_broad
  have h_main := paper_weak_planiness_from_narrow
    hkappa_pos hF_nonempty narrow hclose_narrow hmult_narrow
  rcases h_main with ⟨selection, selected, planeMap, h_sub_selected, h_mass⟩
  have h_sub_S : PaperIsSubshading selected S := by
    intro i; exact Set.Subset.trans (h_sub_selected i) (narrow.subshading i)
  have h_mass_total : (1 / 8 : ENNReal) * S.mass ≤ selected.mass := by
    have hmass1 : (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := h_mass
    have hmass2 : (1 / 2 : ENNReal) * S.mass ≤ narrow.shading.mass := narrow.mass_lower
    have h_coeff : (1 / 4 : ENNReal) * (1 / 2 : ENNReal) = (1 / 8 : ENNReal) := by
      simp only [one_div]
      have hmul : (4 : ENNReal) * (2 : ENNReal) = (8 : ENNReal) := by norm_num
      have hinv : ((4 : ENNReal) * (2 : ENNReal))⁻¹ = (4 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
        rw [ENNReal.mul_inv] <;> simp
      rw [hmul] at hinv; exact hinv.symm
    calc
      (1 / 8 : ENNReal) * S.mass
        = ((1 / 4 : ENNReal) * (1 / 2 : ENNReal)) * S.mass := by rw [h_coeff]
      _ = (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * S.mass) := by rw [mul_assoc]
      _ ≤ (1 / 4 : ENNReal) * narrow.shading.mass := by
        exact mul_le_mul_of_nonneg_left hmass2 (by positivity)
      _ ≤ selected.mass := hmass1
  exact ⟨selected, planeMap, h_sub_S, h_mass_total⟩

end Kakeya.Assouad

end
