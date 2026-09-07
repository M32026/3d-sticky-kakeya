module

/-
  Bounded productProp from A.7 axiom — Helpers part 1b.

  Contains: dual injectivity, packing/covering lemmas, tube family
  construction, translation and scaling of S-sets.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1a
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.CoveringUtils
open DiscretisedFurstenbergEstimate.Translation

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate.CoveringUtils


/-- The appendix dual is injective on dyadic cubes at a fixed positive scale. -/
lemma appendixDualOfParameterSet_injective_on_dyadicCubes (δ : ℝ) (hδ : 0 < δ) :
    Set.InjOn (fun (k : Fin 2 → ℤ) => appendixDualOfParameterSet (dyadicCube δ k)) Set.univ := by
  intro k1 _ k2 _ h_eq
  -- Helper: for y > 0, characterize the x-slice of the dual of cube k at height y.
  have h_slice : ∀ (k : Fin 2 → ℤ) (y : ℝ), 0 < y →
      {x : ℝ | ∃ (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ dyadicCube δ k ∧ x = p 0 * y + p 1} =
      Set.Ico (δ * (k 0 : ℝ) * y + δ * (k 1 : ℝ))
              (δ * ((k 0 : ℝ) + 1) * y + δ * ((k 1 : ℝ) + 1)) := by
    intro k y hy
    let a0 : ℝ := δ * (k 0 : ℝ)
    let a1 : ℝ := δ * ((k 0 : ℝ) + 1)
    let b0 : ℝ := δ * (k 1 : ℝ)
    let b1 : ℝ := δ * ((k 1 : ℝ) + 1)
    have ha : a0 < a1 := by simp [a0, a1, hδ] <;> linarith
    have hb : b0 < b1 := by simp [b0, b1, hδ] <;> linarith
    have hdenom_pos : 0 < a1 * y + b1 - (a0 * y + b0) := by
      have h : a1 * y + b1 - (a0 * y + b0) = δ * (y + 1) := by
        simp [a0, a1, b0, b1] <;> ring
      rw [h]
      positivity
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · -- Forward direction
      rintro ⟨p, hp, rfl⟩
      have h1 : a0 ≤ p 0 := (hp 0).1
      have h2 : p 0 < a1 := (hp 0).2
      have h3 : b0 ≤ p 1 := (hp 1).1
      have h4 : p 1 < b1 := (hp 1).2
      have h5 : a0 * y + b0 ≤ p 0 * y + p 1 := by
        have h51 : a0 * y ≤ p 0 * y := by gcongr
        linarith
      have h6 : p 0 * y + p 1 < a1 * y + b1 := by
        have h61 : p 0 * y < a1 * y := by gcongr
        linarith
      exact ⟨h5, h6⟩
    · -- Backward direction
      rintro ⟨h5, h6⟩
      let denom : ℝ := a1 * y + b1 - (a0 * y + b0)
      let t : ℝ := (x - (a0 * y + b0)) / denom
      have ht0 : 0 ≤ t := by
        apply div_nonneg
        · linarith
        · positivity
      have ht1 : t < 1 := by
        have h : (x - (a0 * y + b0)) < denom := by linarith
        have hdenom_pos' : 0 < denom := hdenom_pos
        calc t = (x - (a0 * y + b0)) / denom := rfl
          _ < denom / denom := by gcongr
          _ = 1 := by field_simp [hdenom_pos'.ne'] <;> ring
      let a : ℝ := a0 + t * δ
      let b : ℝ := b0 + t * δ
      have ha0 : a0 ≤ a := by
        dsimp only [a]
        have h : 0 ≤ t * δ := by positivity
        linarith
      have ha1 : a < a1 := by
        dsimp only [a, a1]
        have h : t * δ < δ := mul_lt_of_lt_one_left hδ ht1
        linarith
      have hb0 : b0 ≤ b := by
        dsimp only [b]
        have h : 0 ≤ t * δ := by positivity
        linarith
      have hb1 : b < b1 := by
        dsimp only [b, b1]
        have h : t * δ < δ := mul_lt_of_lt_one_left hδ ht1
        linarith
      have hdenom_eq : denom = δ * (y + 1) := by
        dsimp only [denom, a0, a1, b0, b1] <;> ring
      have hdenom_ne : denom ≠ 0 := hdenom_pos.ne'
      have h_eq2 : a * y + b = x := by
        dsimp only [a, b, t]
        rw [hdenom_eq]
        have hpos : 0 < δ * (y + 1) := by positivity
        field_simp [hpos.ne'] <;> ring
      let p : EuclideanSpace ℝ (Fin 2) := toEuclidean (a, b)
      have hp0 : p 0 = a := (toEuclidean_apply (a, b)).1
      have hp1 : p 1 = b := (toEuclidean_apply (a, b)).2
      have hp_in : p ∈ dyadicCube δ k := by
        intro i
        fin_cases i <;> simp [hp0, hp1, ha0, ha1, hb0, hb1] <;> tauto
      exact ⟨p, hp_in, Eq.symm h_eq2⟩
  -- For any y > 0, equality of dual sets implies equality of slices.
  have h_slices_eq : ∀ (y : ℝ), 0 < y →
      Set.Ico (δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ))
              (δ * ((k1 0 : ℝ) + 1) * y + δ * ((k1 1 : ℝ) + 1)) =
      Set.Ico (δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ))
              (δ * ((k2 0 : ℝ) + 1) * y + δ * ((k2 1 : ℝ) + 1)) := by
    intro y hy
    have h1 : {x : ℝ | ∃ (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ dyadicCube δ k1 ∧ x = p 0 * y + p 1} =
        {x : ℝ | ∃ (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ dyadicCube δ k2 ∧ x = p 0 * y + p 1} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have h_iff1 : (∃ (p : EuclideanSpace ℝ (Fin 2)),
          p ∈ dyadicCube δ k1 ∧ x = p 0 * y + p 1) ↔
          (∃ (q : EuclideanSpace ℝ (Fin 2)),
          q ∈ appendixDualOfParameterSet (dyadicCube δ k1) ∧ q 1 = y ∧ q 0 = x) := by
        constructor
        · rintro ⟨p, hp, rfl⟩
          let q : EuclideanSpace ℝ (Fin 2) := toEuclidean (p 0 * y + p 1, y)
          have hq0 : q 0 = p 0 * y + p 1 := (toEuclidean_apply (p 0 * y + p 1, y)).1
          have hq1 : q 1 = y := (toEuclidean_apply (p 0 * y + p 1, y)).2
          have hq_in : q ∈ appendixDualOfParameterSet (dyadicCube δ k1) := by
            simp only [appendixDualOfParameterSet, Set.mem_setOf_eq]
            exact ⟨p, hp, by simp [appendixDualLineMap, appendixDualLine, hq0, hq1]⟩
          exact ⟨q, hq_in, hq1, hq0⟩
        · rintro ⟨q, hq, hq1, rfl⟩
          rcases hq with ⟨p, hp, hline⟩
          have h_eq_line : q 0 = p 0 * q 1 + p 1 := by simpa [appendixDualLineMap, appendixDualLine] using hline
          rw [hq1] at h_eq_line
          exact ⟨p, hp, h_eq_line⟩
      have h_iff2 : (∃ (p : EuclideanSpace ℝ (Fin 2)),
          p ∈ dyadicCube δ k2 ∧ x = p 0 * y + p 1) ↔
          (∃ (q : EuclideanSpace ℝ (Fin 2)),
          q ∈ appendixDualOfParameterSet (dyadicCube δ k2) ∧ q 1 = y ∧ q 0 = x) := by
        constructor
        · rintro ⟨p, hp, rfl⟩
          let q : EuclideanSpace ℝ (Fin 2) := toEuclidean (p 0 * y + p 1, y)
          have hq0 : q 0 = p 0 * y + p 1 := (toEuclidean_apply (p 0 * y + p 1, y)).1
          have hq1 : q 1 = y := (toEuclidean_apply (p 0 * y + p 1, y)).2
          have hq_in : q ∈ appendixDualOfParameterSet (dyadicCube δ k2) := by
            simp only [appendixDualOfParameterSet, Set.mem_setOf_eq]
            exact ⟨p, hp, by simp [appendixDualLineMap, appendixDualLine, hq0, hq1]⟩
          exact ⟨q, hq_in, hq1, hq0⟩
        · rintro ⟨q, hq, hq1, rfl⟩
          rcases hq with ⟨p, hp, hline⟩
          have h_eq_line : q 0 = p 0 * q 1 + p 1 := by simpa [appendixDualLineMap, appendixDualLine] using hline
          rw [hq1] at h_eq_line
          exact ⟨p, hp, h_eq_line⟩
      have h_eq' : appendixDualOfParameterSet (dyadicCube δ k1) = appendixDualOfParameterSet (dyadicCube δ k2) := by
        simpa using h_eq
      rw [h_iff1, h_iff2]
      constructor
      · rintro ⟨q, hq, hq1, hq0⟩
        have hq' : q ∈ appendixDualOfParameterSet (dyadicCube δ k2) := h_eq' ▸ hq
        exact ⟨q, hq', hq1, hq0⟩
      · rintro ⟨q, hq, hq1, hq0⟩
        have hq' : q ∈ appendixDualOfParameterSet (dyadicCube δ k1) := h_eq'.symm ▸ hq
        exact ⟨q, hq', hq1, hq0⟩
    rw [h_slice k1 y hy, h_slice k2 y hy] at h1
    exact h1
  -- Deduce equality of left endpoints for all y > 0.
  have h_left_eq : ∀ (y : ℝ), 0 < y →
      δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ) = δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ) := by
    intro y hy
    have h := h_slices_eq y hy
    have h_a1 : δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ) <
        δ * ((k1 0 : ℝ) + 1) * y + δ * ((k1 1 : ℝ) + 1) := by
      have hdiff : δ * ((k1 0 : ℝ) + 1) * y + δ * ((k1 1 : ℝ) + 1) -
          (δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ)) = δ * (y + 1) := by ring
      have hpos : 0 < δ * (y + 1) := by positivity
      linarith
    have h_l1 : δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ) ∈
        Set.Ico (δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ))
                (δ * ((k1 0 : ℝ) + 1) * y + δ * ((k1 1 : ℝ) + 1)) := by
      exact ⟨by linarith, h_a1⟩
    rw [h] at h_l1
    have h_le1 : δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ) ≤ δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ) := h_l1.1
    have h_a2 : δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ) <
        δ * ((k2 0 : ℝ) + 1) * y + δ * ((k2 1 : ℝ) + 1) := by
      have hdiff : δ * ((k2 0 : ℝ) + 1) * y + δ * ((k2 1 : ℝ) + 1) -
          (δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ)) = δ * (y + 1) := by ring
      have hpos : 0 < δ * (y + 1) := by positivity
      linarith
    have h_l2 : δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ) ∈
        Set.Ico (δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ))
                (δ * ((k2 0 : ℝ) + 1) * y + δ * ((k2 1 : ℝ) + 1)) := by
      exact ⟨by linarith, h_a2⟩
    rw [←h] at h_l2
    have h_le2 : δ * (k1 0 : ℝ) * y + δ * (k1 1 : ℝ) ≤ δ * (k2 0 : ℝ) * y + δ * (k2 1 : ℝ) := h_l2.1
    linarith
  -- Evaluate at y = 1 and y = 2 to get k1 0 = k2 0 and k1 1 = k2 1.
  have h_eq1 := h_left_eq 1 (by norm_num)
  have h_eq2 := h_left_eq 2 (by norm_num)
  have h_div : ∀ (y : ℝ), 0 < y →
      (k1 0 : ℝ) * y + (k1 1 : ℝ) = (k2 0 : ℝ) * y + (k2 1 : ℝ) := by
    intro y hy
    have h := h_left_eq y hy
    apply (mul_right_inj' hδ.ne').mp
    linarith
  have h_k0 : (k1 0 : ℝ) = (k2 0 : ℝ) := by
    have h1 := h_div 1 (by norm_num)
    have h2 := h_div 2 (by norm_num)
    linarith
  have h_k1 : (k1 1 : ℝ) = (k2 1 : ℝ) := by
    have h1 := h_div 1 (by norm_num)
    rw [h_k0] at h1
    linarith
  have h_k0' : k1 0 = k2 0 := by exact_mod_cast h_k0
  have h_k1' : k1 1 = k2 1 := by exact_mod_cast h_k1
  have h_main : k1 = k2 := by
    funext i
    fin_cases i <;> tauto
  exact h_main
/-! ### Helper: 2D packing number finiteness -/

/-- Bounded subsets of ℝ×ℝ have finite external covering number at positive scale. -/
lemma externalCoveringNumber_bounded_prod {ε : NNReal} (hε : 0 < ε)
    {A : Set (ℝ × ℝ)} (hA : Bornology.IsBounded A) :
    Metric.externalCoveringNumber ε A < ⊤ := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]; simp
  · have h_main : ∃ (r : ℝ), 0 ≤ r ∧ A ⊆ Metric.closedBall (0 : ℝ × ℝ) r := by
      have h : ∃ (r : ℝ), A ⊆ Metric.closedBall (0 : ℝ × ℝ) r :=
        (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp hA
      rcases h with ⟨r, hsub⟩
      by_cases hr : 0 ≤ r
      · exact ⟨r, hr, hsub⟩
      · have hneg : r < 0 := by linarith
        have h_empty : Metric.closedBall (0 : ℝ × ℝ) r = ∅ := by
          ext z; simp [Metric.mem_closedBall, hneg] <;> linarith
        rw [h_empty] at hsub
        exfalso
        exact hA_empty (Set.subset_empty_iff.mp hsub)
    rcases h_main with ⟨r, hr, hsub⟩
    have hcompact : IsCompact (Metric.closedBall (0 : ℝ × ℝ) r) :=
      isCompact_closedBall (0 : ℝ × ℝ) r
    have hne : ε ≠ 0 := hε.ne'
    rcases Metric.exists_finite_isCover_of_isCompact hne hcompact with ⟨N, _, hNfin, hNcover⟩
    have hcoverA : Metric.IsCover ε A N := hNcover.anti hsub
    have h1 : Metric.externalCoveringNumber ε A ≤ N.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcoverA
    have h2 : N.encard < ⊤ := Set.Finite.encard_lt_top hNfin
    exact h1.trans_lt h2

/-- Packing number at positive scale is finite for bounded sets in `ℝ × ℝ`. -/
lemma bounded_packing_finite2d {δ : ℝ} (hδ : 0 < δ) {A : Set (ℝ × ℝ)}
    (hA_bdd : Bornology.IsBounded A) :
    Metric.packingNumber (9 * δ).toNNReal A ≠ ⊤ := by
  have hpos : 0 < (9 * δ / 2 : ℝ) := by positivity
  let ε : NNReal := (9 * δ / 2).toNNReal
  have hε : (ε : ℝ) = 9 * δ / 2 := by
    simp [ε, Real.coe_toNNReal', show (0 : ℝ) ≤ 9 * δ / 2 by linarith]
  have hε_pos : 0 < ε := by
    exact NNReal.coe_pos.mp (by rw [hε] <;> exact hpos)
  have hfin : Metric.externalCoveringNumber ε A < ⊤ :=
    externalCoveringNumber_bounded_prod hε_pos hA_bdd
  have h2 : (2 * ε : NNReal) = (9 * δ).toNNReal := by
    apply NNReal.coe_injective
    have h3 : ((2 * ε : NNReal) : ℝ) = 2 * (ε : ℝ) := by simp
    rw [h3, hε]
    have h4 : ((9 * δ).toNNReal : ℝ) = 9 * δ := by
      rw [Real.coe_toNNReal', max_eq_left (by linarith)]
    rw [h4] <;> ring
  have hle : Metric.packingNumber (2 * ε) A ≤ Metric.externalCoveringNumber ε A :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber ε A
  have hle' : Metric.packingNumber (9 * δ).toNNReal A ≤ Metric.externalCoveringNumber ε A := by
    rw [h2] at *; exact hle
  exact ne_top_of_le_ne_top hfin.ne hle'

/-! ### Helper: Covering number of a 9δ-ball -/

/-- The δ-covering number of a 9δ-ball in `ℝ × ℝ` is at most 100. -/
lemma covering_δ_ball_9δ (δ : ℝ) (hδ : 0 < δ) (c : ℝ × ℝ) :
    Metric.externalCoveringNumber δ.toNNReal (Metric.closedBall c (9 * δ)) ≤ 100 := by
  let I : Finset ℕ := Finset.range 10
  let center1 (k : ℕ) : ℝ := c.1 + (((k : ℝ) * 2 - 9) * δ)
  let center2 (l : ℕ) : ℝ := c.2 + (((l : ℝ) * 2 - 9) * δ)
  let centers : Finset (ℝ × ℝ) :=
    I.biUnion fun k => I.image (fun l : ℕ => (center1 k, center2 l))
  have h_card : centers.card ≤ 100 := by
    calc centers.card
      ≤ ∑ k ∈ I, (I.image (fun l : ℕ => (center1 k, center2 l))).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ I, I.card := by gcongr with k _; exact Finset.card_image_le
    _ = I.card * I.card := by simp [Finset.sum_const] <;> ring
    _ = 100 := by simp [I] <;> norm_num
  have h_find : ∀ (x d : ℝ), |x - d| ≤ 9 * δ → ∃ k ∈ I, |x - (d + (((k : ℝ) * 2 - 9) * δ))| ≤ δ := by
    intro x d hx
    let z : ℝ := (x - d + 9 * δ) / (2 * δ)
    have hz0 : 0 ≤ z := by
      have h : -(9 * δ) ≤ x - d := (abs_le.mp hx).1
      have h' : 0 ≤ x - d + 9 * δ := by linarith
      exact div_nonneg h' (by positivity)
    have hz9 : z ≤ 9 := by
      have h : x - d ≤ 9 * δ := (abs_le.mp hx).2
      have h' : x - d + 9 * δ ≤ 18 * δ := by linarith
      calc z = (x - d + 9 * δ) / (2 * δ) := rfl
        _ ≤ (18 * δ) / (2 * δ) := by gcongr
        _ = 9 := by field_simp [hδ.ne'] <;> ring
    let k : ℤ := ⌊z + 1 / 2⌋
    have hk0 : 0 ≤ k := by
      have h : 0 ≤ z + 1 / 2 := by linarith
      exact Int.floor_nonneg.mpr h
    have hk9 : k ≤ 9 := by
      have h : z + 1 / 2 ≤ 9 + 1 / 2 := by linarith
      have h' : (k : ℝ) ≤ z + 1 / 2 := Int.floor_le _
      have h'' : (k : ℝ) ≤ 9 + 1 / 2 := by linarith
      have h3 : k ≤ 9 := by
        by_contra h4
        have h5 : k ≥ 10 := by omega
        have h6 : (k : ℝ) ≥ 10 := by exact_mod_cast h5
        linarith
      exact h3
    have hk_nat : ∃ (kn : ℕ), (kn : ℤ) = k := by
      refine ⟨k.toNat, ?_⟩
      simp [Int.toNat_of_nonneg hk0]
    rcases hk_nat with ⟨kn, hkn_eq⟩
    have hkn_I : kn ∈ I := by
      simp only [I, Finset.mem_range]
      omega
    have h_approx : |z - (k : ℝ)| ≤ 1 / 2 := by
      have h1 : (k : ℝ) ≤ z + 1 / 2 := Int.floor_le _
      have h2 : z + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
      have h3 : -(1 / 2 : ℝ) ≤ z - (k : ℝ) := by linarith
      have h4 : z - (k : ℝ) ≤ 1 / 2 := by linarith
      exact abs_le.mpr ⟨h3, h4⟩
    have h_goal : |x - (d + (((k : ℝ) * 2 - 9) * δ))| ≤ δ := by
      have h_eq : x - (d + (((k : ℝ) * 2 - 9) * δ)) = 2 * δ * (z - (k : ℝ)) := by
        simp [z] <;> field_simp [hδ.ne'] <;> ring
      rw [h_eq]
      have h3 : |2 * δ * (z - (k : ℝ))| = 2 * δ * |z - (k : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity)] <;> ring
      rw [h3]
      have h4 : 2 * δ * |z - (k : ℝ)| ≤ 2 * δ * (1 / 2 : ℝ) := by gcongr
      have h5 : 2 * δ * (1 / 2 : ℝ) = δ := by ring
      rw [h5] at h4; exact h4
    have h_goal' : |x - (d + (((kn : ℝ) * 2 - 9) * δ))| ≤ δ := by
      have hkn : (kn : ℝ) = (k : ℝ) := by exact_mod_cast hkn_eq
      rw [hkn]; exact h_goal
    exact ⟨kn, hkn_I, h_goal'⟩
  have hcover : Metric.IsCover δ.toNNReal (Metric.closedBall c (9 * δ)) (centers : Set (ℝ × ℝ)) := by
    intro p hp
    have hdist : dist p c ≤ 9 * δ := (Metric.mem_closedBall).mp hp
    have h1 : |p.1 - c.1| ≤ 9 * δ := by
      have h : dist p c = max (|p.1 - c.1|) (|p.2 - c.2|) := by simp [Prod.dist_eq] <;> rfl
      rw [h] at hdist; exact le_trans (le_max_left _ _) hdist
    have h2 : |p.2 - c.2| ≤ 9 * δ := by
      have h : dist p c = max (|p.1 - c.1|) (|p.2 - c.2|) := by simp [Prod.dist_eq] <;> rfl
      rw [h] at hdist; exact le_trans (le_max_right _ _) hdist
    rcases h_find p.1 c.1 h1 with ⟨k, hk_I, hk_dist⟩
    rcases h_find p.2 c.2 h2 with ⟨l, hl_I, hl_dist⟩
    let center : ℝ × ℝ := (center1 k, center2 l)
    have hcenter_in : center ∈ centers := by
      simp only [centers, Finset.mem_biUnion]
      refine ⟨k, hk_I, ?_⟩
      simp only [Finset.mem_image]
      refine ⟨l, hl_I, ?_⟩
      rfl
    have hdist_center : dist p center ≤ δ := by
      have h : dist p center = max (|p.1 - center.1|) (|p.2 - center.2|) := by
        simp [Prod.dist_eq] <;> rfl
      rw [h]
      exact max_le hk_dist hl_dist
    have hed : edist p center ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h4 : 0 ≤ δ := by linarith
      have h5 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
        have h7 : (δ.toNNReal : ℝ) = δ := Real.coe_toNNReal δ h4
        have h8 : ENNReal.ofReal ((δ.toNNReal : ℝ)) = (↑δ.toNNReal : ENNReal) :=
          ENNReal.ofReal_coe_nnreal (p := δ.toNNReal)
        rw [h7] at h8
        exact h8.symm
      rw [h5]
      exact ENNReal.ofReal_le_ofReal hdist_center
    exact ⟨center, hcenter_in, hed⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal (Metric.closedBall c (9 * δ)) ≤
      (centers : Set (ℝ × ℝ)).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h2 : (centers : Set (ℝ × ℝ)).encard = ↑centers.card :=
    Set.encard_coe_eq_coe_finsetCard centers
  rw [h2] at h1
  exact h1.trans (by exact_mod_cast h_card)

lemma cover_by_finite_9δ_net {δ : ℝ} (hδ : 0 < δ) {A : Set (ℝ × ℝ)} {S : Finset (ℝ × ℝ)}
    (hcover : A ⊆ ⋃ s ∈ (S : Set (ℝ × ℝ)), Metric.closedBall s (9 * δ)) :
    Metric.externalCoveringNumber δ.toNNReal A ≤ 100 * (S.card : ENat) := by
  let B : ℝ × ℝ → Set (ℝ × ℝ) := fun s => Metric.closedBall s (9 * δ)
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤
      Metric.externalCoveringNumber δ.toNNReal (⋃ s ∈ (S : Set (ℝ × ℝ)), B s) :=
    Metric.externalCoveringNumber_mono_set hcover
  have h2 : Metric.externalCoveringNumber δ.toNNReal (⋃ s ∈ (S : Set (ℝ × ℝ)), B s) ≤
      ∑ s ∈ S, Metric.externalCoveringNumber δ.toNNReal (B s) :=
    externalCoveringNumber_biUnion
  have h3 : ∀ s ∈ S, Metric.externalCoveringNumber δ.toNNReal (B s) ≤ (100 : ENat) :=
    fun s _ => covering_δ_ball_9δ δ hδ s
  have h4 : ∑ s ∈ S, Metric.externalCoveringNumber δ.toNNReal (B s) ≤ ∑ s ∈ S, (100 : ENat) :=
    Finset.sum_le_sum h3
  have h5 : ∑ s ∈ S, (100 : ENat) = 100 * (S.card : ENat) := by
    simp [Finset.sum_const] <;> ring
  calc Metric.externalCoveringNumber δ.toNNReal A
    ≤ Metric.externalCoveringNumber δ.toNNReal (⋃ s ∈ (S : Set (ℝ × ℝ)), B s) := h1
  _ ≤ ∑ s ∈ S, Metric.externalCoveringNumber δ.toNNReal (B s) := h2
  _ ≤ ∑ s ∈ S, (100 : ENat) := h4
  _ = 100 * (S.card : ENat) := h5

/-! ### Helper: every 2D point lies in a dyadic cube -/

lemma exists_dyadicCube2 {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin 2)) :
    ∃ (k : Fin 2 → ℤ), x ∈ dyadicCube δ k := by
  let k0 : ℤ := ⌊x 0 / δ⌋
  let k1 : ℤ := ⌊x 1 / δ⌋
  let k : Fin 2 → ℤ := fun i => if i = 0 then k0 else k1
  have h01 : δ * (k0 : ℝ) ≤ x 0 := by
    have h : (k0 : ℝ) ≤ x 0 / δ := Int.floor_le _
    have h2 : δ * (k0 : ℝ) ≤ δ * (x 0 / δ) := by gcongr
    have h3 : δ * (x 0 / δ) = x 0 := by field_simp [hδ.ne'] <;> ring
    linarith
  have h02 : x 0 < δ * ((k0 : ℝ) + 1) := by
    have h : x 0 / δ < (k0 : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : x 0 = δ * (x 0 / δ) := by field_simp [hδ.ne'] <;> ring
    rw [h2]; gcongr <;> linarith
  have h11 : δ * (k1 : ℝ) ≤ x 1 := by
    have h : (k1 : ℝ) ≤ x 1 / δ := Int.floor_le _
    have h2 : δ * (k1 : ℝ) ≤ δ * (x 1 / δ) := by gcongr
    have h3 : δ * (x 1 / δ) = x 1 := by field_simp [hδ.ne'] <;> ring
    linarith
  have h12 : x 1 < δ * ((k1 : ℝ) + 1) := by
    have h : x 1 / δ < (k1 : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : x 1 = δ * (x 1 / δ) := by field_simp [hδ.ne'] <;> ring
    rw [h2]; gcongr <;> linarith
  refine ⟨k, ?_⟩
  intro i
  fin_cases i <;> simp [k, h01, h02, h11, h12] <;> tauto

/-! ### Helper: canonical cube equals original -/

lemma canonicalCube_equals_original {δ : ℝ} (hδ : 0 < δ)
    {k : Fin 2 → ℤ}
    (hk : dyadicCube δ k ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip) :
    productLikeAppendixDyadicTubeCanonicalParameterCube δ
      (appendixDualOfParameterSet (dyadicCube δ k)) = dyadicCube δ k := by
  let T := appendixDualOfParameterSet (dyadicCube δ k)
  have hT : T ∈ appendixDyadicTubes δ := ⟨dyadicCube δ k, hk, rfl⟩
  have h_main : productLikeAppendixDyadicTubeCanonicalParameterCube δ T ∈
      dyadicCubesMeeting (d := 2) δ appendixParameterStrip ∧
      appendixDualOfParameterSet (productLikeAppendixDyadicTubeCanonicalParameterCube δ T) = T := by
    simpa [productLikeAppendixDyadicTubeCanonicalParameterCube, dif_pos hT] using
      Classical.choose_spec hT
  rcases h_main with ⟨hP''1, hP''2⟩
  have hP''in_cubes : productLikeAppendixDyadicTubeCanonicalParameterCube δ T ∈ dyadicCubes (d := 2) δ :=
    hP''1.1
  rcases hP''in_cubes with ⟨k', hk'⟩
  have h_dual : appendixDualOfParameterSet (dyadicCube δ k') =
      appendixDualOfParameterSet (dyadicCube δ k) := by
    rw [←hk', hP''2]
  have h_inj := appendixDualOfParameterSet_injective_on_dyadicCubes δ hδ
  have h_k_eq : k' = k := h_inj (by simp) (by simp) h_dual
  rw [hk', h_k_eq]

lemma canonicalCube_equals_original' {δ : ℝ} (hδ : 0 < δ)
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : P ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip) :
    productLikeAppendixDyadicTubeCanonicalParameterCube δ (appendixDualOfParameterSet P) = P := by
  rcases hP.1 with ⟨k, hk⟩
  have hP' : P = dyadicCube δ k := hk
  subst hP'
  exact canonicalCube_equals_original hδ hP

/-! ### Helper: finite dyadic cubes meeting bounded set -/

lemma finite_dyadicCubes_meeting_bounded {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A) :
    Set.Finite {k : Fin 2 → ℤ | (dyadicCube δ k ∩ A).Nonempty} := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mp hA with ⟨R, hR⟩
  let R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hR2 : A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R' := by
    have h1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R' := by
      intro x hx
      have h2 : dist x (0 : EuclideanSpace ℝ (Fin 2)) ≤ R := by simpa [Metric.mem_closedBall] using hx
      have h3 : R ≤ R' := le_max_left _ _
      simpa [Metric.mem_closedBall] using h2.trans h3
    exact hR.trans h1
  have h1 : ∀ k, (dyadicCube δ k ∩ A).Nonempty → ∀ i : Fin 2, (k i : ℝ) ∈ Set.Icc (-R' / δ - 1) (R' / δ + 1) := by
    intro k hk i
    rcases hk with ⟨x, hx_cube, hx_A⟩
    have h2 : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R' := hR2 hx_A
    have h3 : ‖x‖ ≤ R' := by simpa [Metric.mem_closedBall] using h2
    have h4 : |x i| ≤ ‖x‖ := by exact DiscretisedFurstenbergEstimate.DyadicCubes.DyadicCube.coord_abs_le_norm x i
    have h41 : -R' ≤ x i := (abs_le.mp (h4.trans h3)).1
    have h42 : x i ≤ R' := (abs_le.mp (h4.trans h3)).2
    have h6 : δ * (k i : ℝ) ≤ x i := (hx_cube i).1
    have h7 : x i < δ * ((k i : ℝ) + 1) := (hx_cube i).2
    constructor
    · have h8 : -R' < δ * ((k i : ℝ) + 1) := by linarith
      have h9 : (k i : ℝ) + 1 > -R' / δ := by
        calc (k i : ℝ) + 1 = (δ * ((k i : ℝ) + 1)) / δ := by field_simp [hδ.ne'] <;> ring
          _ > (-R') / δ := by gcongr
      linarith
    · have h8 : (k i : ℝ) ≤ R' / δ := by
        calc (k i : ℝ) = (δ * (k i : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
          _ ≤ x i / δ := by gcongr
          _ ≤ R' / δ := by gcongr
      linarith
  let K0 : Finset ℤ := Finset.Icc ⌊-R' / δ - 1⌋ ⌈R' / δ + 1⌉
  let K1 : Finset ℤ := Finset.Icc ⌊-R' / δ - 1⌋ ⌈R' / δ + 1⌉
  let S' : Finset (Fin 2 → ℤ) := K0.biUnion fun k0 => K1.image fun k1 =>
    (fun i : Fin 2 => if i = 0 then k0 else k1)
  have h_sub : {k : Fin 2 → ℤ | (dyadicCube δ k ∩ A).Nonempty} ⊆ (S' : Set (Fin 2 → ℤ)) := by
    intro k hk
    have h41 : (k 0 : ℝ) ≥ -R' / δ - 1 := (h1 k hk 0).1
    have h42 : (k 0 : ℝ) ≤ R' / δ + 1 := (h1 k hk 0).2
    have h51 : (k 1 : ℝ) ≥ -R' / δ - 1 := (h1 k hk 1).1
    have h52 : (k 1 : ℝ) ≤ R' / δ + 1 := (h1 k hk 1).2
    have h_k0_lo : ⌊-R' / δ - 1⌋ ≤ k 0 := by
      have h : (⌊-R' / δ - 1⌋ : ℝ) ≤ -R' / δ - 1 := Int.floor_le _
      exact_mod_cast show (⌊-R' / δ - 1⌋ : ℝ) ≤ (k 0 : ℝ) from by linarith
    have h_k0_hi : k 0 ≤ ⌈R' / δ + 1⌉ := by
      have h : (R' / δ + 1 : ℝ) ≤ ⌈R' / δ + 1⌉ := Int.le_ceil _
      exact_mod_cast show (k 0 : ℝ) ≤ (⌈R' / δ + 1⌉ : ℝ) from by linarith
    have h_k1_lo : ⌊-R' / δ - 1⌋ ≤ k 1 := by
      have h : (⌊-R' / δ - 1⌋ : ℝ) ≤ -R' / δ - 1 := Int.floor_le _
      exact_mod_cast show (⌊-R' / δ - 1⌋ : ℝ) ≤ (k 1 : ℝ) from by linarith
    have h_k1_hi : k 1 ≤ ⌈R' / δ + 1⌉ := by
      have h : (R' / δ + 1 : ℝ) ≤ ⌈R' / δ + 1⌉ := Int.le_ceil _
      exact_mod_cast show (k 1 : ℝ) ≤ (⌈R' / δ + 1⌉ : ℝ) from by linarith
    have h_k0_in : k 0 ∈ K0 := by
      simp only [K0, Finset.mem_Icc]; exact ⟨h_k0_lo, h_k0_hi⟩
    have h_k1_in : k 1 ∈ K1 := by
      simp only [K1, Finset.mem_Icc]; exact ⟨h_k1_lo, h_k1_hi⟩
    simp only [S', Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨k 0, h_k0_in, ?_⟩
    simp only [Finset.mem_image]
    refine ⟨k 1, h_k1_in, ?_⟩
    funext i; fin_cases i <;> simp
  exact Set.Finite.subset (Finset.finite_toSet S') h_sub

/-! ### Helper: cube index difference bound for nearby points -/

lemma cube_index_diff_le_3 {δ : ℝ} (hδ : 0 < δ)
    {x y : EuclideanSpace ℝ (Fin 2)}
    {k_x k_y : Fin 2 → ℤ}
    (hx : x ∈ dyadicCube δ k_x)
    (hy : y ∈ dyadicCube δ k_y)
    (h_dist : ‖x - y‖ ≤ 2 * Real.sqrt 2 * δ) :
    ∀ (i : Fin 2), |(k_x i : ℤ) - (k_y i : ℤ)| ≤ 3 := by
  have h3 : 2 * Real.sqrt 2 * δ < 3 * δ := by
    have h4 : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith
  intro i
  have h1 : |x i - y i| ≤ ‖x - y‖ := by
    have h2 : (x i - y i)^2 ≤ ‖x - y‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have h3 : (x i - y i)^2 ≤ ∑ j : Fin 2, (x j - y j)^2 := by
        exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (x j - y j)^2) (fun j _ => by positivity) (Finset.mem_univ i)
      exact h3
    have h4 : 0 ≤ |x i - y i| := by positivity
    have h5 : 0 ≤ ‖x - y‖ := by positivity
    have h6 : |x i - y i|^2 ≤ ‖x - y‖^2 := by
      have h7 : |x i - y i|^2 = (x i - y i)^2 := by rw [sq_abs]
      rw [h7]; exact h2
    nlinarith [h6]
  have h2 : |x i - y i| < 3 * δ := by
    calc |x i - y i| ≤ ‖x - y‖ := h1
      _ ≤ 2 * Real.sqrt 2 * δ := h_dist
      _ < 3 * δ := h3
  by_cases h4 : (k_x i : ℝ) ≥ (k_y i : ℝ) + 4
  · have h5 : x i ≥ δ * (k_x i : ℝ) := (hx i).1
    have h6 : y i < δ * ((k_y i : ℝ) + 1) := (hy i).2
    have h71 : δ * (k_x i : ℝ) ≥ δ * ((k_y i : ℝ) + 4) := by
      exact mul_le_mul_of_nonneg_left h4 (by linarith [hδ])
    have h7 : x i - y i > 3 * δ := by
      have h72 : x i ≥ δ * ((k_y i : ℝ) + 4) := by linarith
      linarith
    have h8 : |x i - y i| > 3 * δ := by
      have h_pos : 0 < x i - y i := by linarith
      rw [abs_of_pos h_pos] <;> linarith
    linarith
  · by_cases h5 : (k_y i : ℝ) ≥ (k_x i : ℝ) + 4
    · have h6 : y i ≥ δ * (k_y i : ℝ) := (hy i).1
      have h7 : x i < δ * ((k_x i : ℝ) + 1) := (hx i).2
      have h71 : δ * (k_y i : ℝ) ≥ δ * ((k_x i : ℝ) + 4) := by
        exact mul_le_mul_of_nonneg_left h5 (by linarith [hδ])
      have h8 : y i - x i > 3 * δ := by
        have h72 : y i ≥ δ * ((k_x i : ℝ) + 4) := by linarith
        linarith
      have h9 : |x i - y i| > 3 * δ := by
        have h10 : 0 < y i - x i := by linarith
        have h11 : |x i - y i| = |y i - x i| := by rw [abs_sub_comm]
        rw [h11, abs_of_pos h10] <;> linarith
      linarith
    · have h6 : (k_x i : ℝ) < (k_y i : ℝ) + 4 := by linarith
      have h7 : (k_y i : ℝ) < (k_x i : ℝ) + 4 := by linarith
      have h8 : -4 < (k_x i : ℝ) - (k_y i : ℝ) := by linarith
      have h9 : (k_x i : ℝ) - (k_y i : ℝ) < 4 := by linarith
      have h10 : -4 < (k_x i - k_y i : ℤ) := by exact_mod_cast h8
      have h11 : (k_x i - k_y i : ℤ) < 4 := by exact_mod_cast h9
      have h12 : |(k_x i - k_y i : ℤ)| ≤ 3 := by
        rw [abs_le] <;> constructor <;> linarith
      exact h12

/-! ### Helper: dyadic cube is bounded -/

lemma dyadicCube_bounded {δ : ℝ} (hδ : 0 < δ) {k : Fin 2 → ℤ} :
    Bornology.IsBounded (dyadicCube δ k) := by
  let cT : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => δ * ((k i : ℝ) + 1 / 2))
  have h : dyadicCube δ k ⊆ Metric.closedBall cT δ := by
    intro x hx
    have h3 : ∀ i : Fin 2, |x i - δ * ((k i : ℝ) + 1 / 2)| ≤ δ / 2 := by
      intro i
      have h4 : δ * (k i : ℝ) ≤ x i := (hx i).1
      have h5 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h4 : ‖x - cT‖ ≤ δ := by
      have h5 : ‖x - cT‖ ^ 2 ≤ ∑ i : Fin 2, (δ / 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        apply Finset.sum_le_sum
        intro i _
        have h6 : (x i - δ * ((k i : ℝ) + 1 / 2)) ^ 2 ≤ (δ / 2) ^ 2 := by
          have h7 : |x i - δ * ((k i : ℝ) + 1 / 2)| ≤ δ / 2 := h3 i
          have h8 : (x i - δ * ((k i : ℝ) + 1 / 2)) ^ 2 = |x i - δ * ((k i : ℝ) + 1 / 2)| ^ 2 := by rw [sq_abs]
          rw [h8]; gcongr
        exact h6
      have h9 : (∑ i : Fin 2, (δ / 2) ^ 2) = δ ^ 2 / 2 := by
        simp [Finset.sum_const] <;> ring
      rw [h9] at h5
      have h10 : 0 ≤ ‖x - cT‖ := by positivity
      nlinarith
    exact h4
  exact Metric.isBounded_closedBall.subset h

/-! ### Helper: intersecting dyadic cubes have equal indices -/

lemma dyadicCube_inter_eq {δ : ℝ} (hδ : 0 < δ) {k1 k2 : Fin 2 → ℤ}
    (h : (dyadicCube δ k1 ∩ dyadicCube δ k2).Nonempty) : k1 = k2 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h_i : ∀ i : Fin 2, (k1 i : ℝ) = (k2 i : ℝ) := by
    intro i
    have h1 : δ * (k1 i : ℝ) ≤ x i := (hx1 i).1
    have h2 : x i < δ * ((k1 i : ℝ) + 1) := (hx1 i).2
    have h3 : δ * (k2 i : ℝ) ≤ x i := (hx2 i).1
    have h4 : x i < δ * ((k2 i : ℝ) + 1) := (hx2 i).2
    by_cases hne : (k1 i : ℝ) < (k2 i : ℝ)
    · have hne' : k1 i < k2 i := by exact_mod_cast hne
      have h5 : (k1 i : ℝ) + 1 ≤ (k2 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hne'
      have h6 : δ * ((k1 i : ℝ) + 1) ≤ δ * (k2 i : ℝ) := by gcongr
      linarith
    · by_cases hne2 : (k2 i : ℝ) < (k1 i : ℝ)
      · have hne2' : k2 i < k1 i := by exact_mod_cast hne2
        have h5 : (k2 i : ℝ) + 1 ≤ (k1 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt hne2'
        have h6 : δ * ((k2 i : ℝ) + 1) ≤ δ * (k1 i : ℝ) := by gcongr
        linarith
      · have h_eq : (k1 i : ℝ) = (k2 i : ℝ) := by linarith
        exact h_eq
  funext i
  exact_mod_cast h_i i

/-! ### Helper: index set near fixed index has size ≤ 49 -/

lemma index_set_near_bound_49 {K : Set (Fin 2 → ℤ)} {k0 : Fin 2 → ℤ}
    (h_main : ∀ k ∈ K, ∀ i : Fin 2, |(k i : ℤ) - (k0 i : ℤ)| ≤ 3) :
    K.encard ≤ 49 := by
  let S : Finset (Fin 2 → ℤ) :=
    Fintype.piFinset fun i : Fin 2 => Finset.Icc (k0 i - 3) (k0 i + 3)
  have hK_sub : K ⊆ (S : Set (Fin 2 → ℤ)) := by
    intro k hk
    have h1 : ∀ i : Fin 2, k i ∈ Finset.Icc (k0 i - 3) (k0 i + 3) := by
      intro i
      have h2 : |(k i : ℤ) - (k0 i : ℤ)| ≤ 3 := h_main k hk i
      have h3 : k0 i - 3 ≤ k i := by
        have h4 : -3 ≤ (k i : ℤ) - (k0 i : ℤ) := by linarith [abs_le.mp h2]
        linarith
      have h5 : k i ≤ k0 i + 3 := by
        have h6 : (k i : ℤ) - (k0 i : ℤ) ≤ 3 := by linarith [abs_le.mp h2]
        linarith
      exact Finset.mem_Icc.mpr ⟨h3, h5⟩
    have h2 : k ∈ S := by
      rw [Fintype.mem_piFinset]
      exact h1
    exact h2
  have h_fin : Set.Finite K := Set.Finite.subset (Finset.finite_toSet S) hK_sub
  have h_encard : K.encard ≤ (S : Set (Fin 2 → ℤ)).encard := Set.encard_le_encard hK_sub
  have h_card : S.card = 49 := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ (i : Fin 2), Finset.card (Finset.Icc (k0 i - 3) (k0 i + 3)) = 7 := by
      intro i
      rw [Int.card_Icc]
      have h2 : (k0 i + 3 + 1 - (k0 i - 3)) = (7 : ℤ) := by ring
      rw [h2]
      have h3 : Int.toNat (7 : ℤ) = 7 := by decide
      exact h3
    rw [Fin.prod_univ_two, h1 0, h1 1] <;> norm_num
  have h_set_card : (S : Set (Fin 2 → ℤ)).encard = (S.card : ENat) := by
    exact Set.encard_coe_eq_coe_finsetCard S
  rw [h_set_card] at h_encard
  rw [h_card] at h_encard
  exact h_encard

/-! ### Helper: encard of finite biUnion bounded by sum -/

lemma encard_biUnion_le_sum {α ι : Type*} [DecidableEq α]
    (s : Finset ι) (t : ι → Set α) :
    (⋃ i ∈ s, t i).encard ≤ ∑ i ∈ s, (t i).encard := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h_union : (⋃ i ∈ (insert a s), t i) = t a ∪ (⋃ i ∈ s, t i) := by
      ext x; simp [ha, Set.mem_iUnion] <;> tauto
    rw [h_union]
    have h1 : (t a ∪ ⋃ i ∈ s, t i).encard ≤ (t a).encard + (⋃ i ∈ s, t i).encard :=
      Set.encard_union_le _ _
    have h2 : (⋃ i ∈ s, t i).encard ≤ ∑ i ∈ s, (t i).encard := ih
    have h3 : (t a).encard + (⋃ i ∈ s, t i).encard ≤ (t a).encard + ∑ i ∈ s, (t i).encard := by gcongr
    have h4 : ∑ i ∈ insert a s, (t i).encard = (t a).encard + ∑ i ∈ s, (t i).encard := by
      rw [Finset.sum_insert ha]
    rw [h4]
    exact h1.trans h3

/-! ### K_Q encard bound: |K_Q| ≤ 49 * |C_cover| -/

lemma kq_encard_bound {δ : ℝ} (hδ : 0 < δ)
    {Tz : Set (ℝ × ℝ)}
    {Indices : Set (Fin 2 → ℤ)}
    {rep : (Fin 2 → ℤ) → ℝ × ℝ}
    {k_p : (ℝ × ℝ) → (Fin 2 → ℤ)}
    {f : ℝ × ℝ → ℝ × ℝ}
    {e : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)}
    {K_Q : Set (Fin 2 → ℤ)}
    (hKQ_fin : Set.Finite K_Q)
    {C_cover : Set (ℝ × ℝ)}
    {c_Q' : ℝ × ℝ}
    {r : ℝ}
    (hKQ_sub : K_Q ⊆ Indices)
    (hrep1 : ∀ k ∈ Indices, rep k ∈ Tz)
    (hrep2 : ∀ k ∈ Indices, k_p (rep k) = k)
    (hk_p : ∀ p ∈ Tz, e (f p) ∈ dyadicCube δ (k_p p))
    (h_f_lip : LipschitzWith 1 f)
    (h_e_lip : LipschitzWith ⟨Real.sqrt 2, by positivity⟩ e)
    (h_rep_in_ball : ∀ k ∈ K_Q, rep k ∈ Metric.closedBall c_Q' (2 * r))
    (hC_cover : Metric.IsCover δ.toNNReal (Tz ∩ Metric.closedBall c_Q' (2 * r)) C_cover) :
    ENat.toENNReal K_Q.encard ≤ (49 : ENNReal) * ENat.toENNReal C_cover.encard := by
  by_cases hfin : Set.Finite C_cover
  · let C_fin := hfin.toFinset
    have hC_eq : (C_fin : Set (ℝ × ℝ)) = C_cover := by
      ext x; simp [C_fin]
    let K_c : ℝ × ℝ → Set (Fin 2 → ℤ) := fun c =>
      {k ∈ K_Q | rep k ∈ Metric.closedBall c δ}
    have hK_c_fin : ∀ c ∈ C_fin, Set.Finite (K_c c) := fun c _ =>
      Set.Finite.subset hKQ_fin (fun k hk => hk.1)
    have h_union : K_Q ⊆ ⋃ c ∈ C_fin, K_c c := by
      intro k hk
      have h1 : rep k ∈ Tz ∩ Metric.closedBall c_Q' (2 * r) :=
        ⟨hrep1 k (hKQ_sub hk), h_rep_in_ball k hk⟩
      rcases hC_cover h1 with ⟨c, hc, h_edist⟩
      have h_nndist : nndist (rep k) c ≤ δ.toNNReal := edist_le_coe.mp h_edist
      have h_dist : dist (rep k) c ≤ (δ.toNNReal : ℝ) := dist_le_coe.mpr h_nndist
      have h0 : 0 ≤ δ := by linarith
      have hδ' : (δ.toNNReal : ℝ) = δ := by
        rw [Real.coe_toNNReal', max_eq_left h0]
      rw [hδ'] at h_dist
      have hc' : c ∈ C_fin := by
        have h : c ∈ (C_fin : Set (ℝ × ℝ)) := by
          rw [hC_eq]
          exact hc
        exact_mod_cast h
      have h_goal : k ∈ K_c c := ⟨hk, h_dist⟩
      exact Set.mem_iUnion₂.mpr ⟨c, hc', h_goal⟩
    have h_49 : ∀ c ∈ C_fin, (K_c c).encard ≤ 49 := by
      intro c _
      by_cases h_empty : K_c c = ∅
      · rw [h_empty]; simp
      · rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨k0, hk0⟩
        have h_main : ∀ k ∈ K_c c, ∀ i : Fin 2, |(k i : ℤ) - (k0 i : ℤ)| ≤ 3 := by
          intro k hk i
          have h1 : rep k ∈ Metric.closedBall c δ := hk.2
          have h2 : rep k0 ∈ Metric.closedBall c δ := hk0.2
          have h3 : dist (rep k) (rep k0) ≤ 2 * δ := by
            calc dist (rep k) (rep k0)
              ≤ dist (rep k) c + dist c (rep k0) := dist_triangle _ _ _
            _ = dist (rep k) c + dist (rep k0) c := by rw [dist_comm c (rep k0)]
            _ ≤ δ + δ := by
              have h4 : dist (rep k) c ≤ δ := by simpa [Metric.mem_closedBall] using h1
              have h5 : dist (rep k0) c ≤ δ := by simpa [Metric.mem_closedBall] using h2
              linarith
            _ = 2 * δ := by ring
          have h4 : dist (f (rep k)) (f (rep k0)) ≤ 2 * δ := by
            have h5 : dist (f (rep k)) (f (rep k0)) ≤ ↑1 * dist (rep k) (rep k0) :=
              h_f_lip.dist_le_mul (rep k) (rep k0)
            have h5' : dist (f (rep k)) (f (rep k0)) ≤ dist (rep k) (rep k0) := by simpa using h5
            exact h5'.trans h3
          have h6 : ‖e (f (rep k)) - e (f (rep k0))‖ ≤ 2 * Real.sqrt 2 * δ := by
            have h7 := h_e_lip.dist_le_mul (f (rep k)) (f (rep k0))
            calc ‖e (f (rep k)) - e (f (rep k0))‖
              ≤ Real.sqrt 2 * dist (f (rep k)) (f (rep k0)) := h7
            _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr
            _ = 2 * Real.sqrt 2 * δ := by ring
          have hkin : k ∈ Indices := hKQ_sub hk.1
          have hk0in : k0 ∈ Indices := hKQ_sub hk0.1
          have h8 : e (f (rep k)) ∈ dyadicCube δ k := by
            have h9 : e (f (rep k)) ∈ dyadicCube δ (k_p (rep k)) := hk_p (rep k) (hrep1 k hkin)
            have h10 : k_p (rep k) = k := hrep2 k hkin
            rw [h10] at h9
            exact h9
          have h11 : e (f (rep k0)) ∈ dyadicCube δ k0 := by
            have h12 : e (f (rep k0)) ∈ dyadicCube δ (k_p (rep k0)) := hk_p (rep k0) (hrep1 k0 hk0in)
            have h13 : k_p (rep k0) = k0 := hrep2 k0 hk0in
            rw [h13] at h12
            exact h12
          exact cube_index_diff_le_3 hδ h8 h11 h6 i
        exact index_set_near_bound_49 h_main
    have h_encard_union : (⋃ c ∈ C_fin, K_c c).encard ≤ ∑ c ∈ C_fin, (K_c c).encard :=
      encard_biUnion_le_sum C_fin K_c
    have h_sum : ∑ c ∈ C_fin, (K_c c).encard ≤ ∑ c ∈ C_fin, (49 : ENat) := by
      apply Finset.sum_le_sum; intro c hc; exact h_49 c hc
    have h_sum2 : ∑ c ∈ C_fin, (49 : ENat) = (49 : ENat) * ↑C_fin.card := by
      simp [Finset.sum_const] <;> ring
    have hKQ_le : K_Q.encard ≤ (⋃ c ∈ C_fin, K_c c).encard :=
      Set.encard_le_encard h_union
    calc ENat.toENNReal K_Q.encard
      ≤ ENat.toENNReal (⋃ c ∈ C_fin, K_c c).encard := by exact_mod_cast hKQ_le
    _ ≤ ENat.toENNReal (∑ c ∈ C_fin, (K_c c).encard) := by exact_mod_cast h_encard_union
    _ ≤ ENat.toENNReal (∑ c ∈ C_fin, (49 : ENat)) := by exact_mod_cast h_sum
    _ = (49 : ENNReal) * ENat.toENNReal C_cover.encard := by
      rw [h_sum2]
      have h_eq : ENat.toENNReal C_cover.encard = ↑C_fin.card := by
        have h13 : C_cover = (C_fin : Set (ℝ × ℝ)) := hC_eq.symm
        rw [h13]
        simp
      rw [h_eq] <;> norm_cast <;> ring
  · have h_inf : C_cover.encard = ⊤ := by
      have h : ¬Set.Finite C_cover := hfin
      exact Set.encard_eq_top_iff.mpr h
    rw [h_inf]
    simp
/-! ### Helper: 2D S-set → tube family with exact incidence -/

/-- Two points in the same dyadic cube of side δ have Euclidean distance ≤ sqrt(2)*δ. -/
lemma dyadicCube_diameter_bound {δ : ℝ} (hδ : 0 < δ) {k : Fin 2 → ℤ}
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ dyadicCube δ k) (hy : y ∈ dyadicCube δ k) :
    ‖x - y‖ ≤ Real.sqrt 2 * δ := by
  have h1 : ∀ i : Fin 2, |x i - y i| < δ := by
    intro i
    have hx1 : δ * (k i : ℝ) ≤ x i := (hx i).1
    have hx2 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
    have hy1 : δ * (k i : ℝ) ≤ y i := (hy i).1
    have hy2 : y i < δ * ((k i : ℝ) + 1) := (hy i).2
    rw [abs_sub_lt_iff] <;> constructor <;> linarith
  have h2 : ‖x - y‖ ^ 2 = |x 0 - y 0| ^ 2 + |x 1 - y 1| ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq] <;> ring
  have h3 : ‖x - y‖ ^ 2 ≤ 2 * δ ^ 2 := by
    rw [h2]
    have h4 : |x 0 - y 0| ^ 2 ≤ δ ^ 2 := by
      have h5 : |x 0 - y 0| ≤ δ := by linarith [h1 0]
      have h6 : 0 ≤ |x 0 - y 0| := by positivity
      nlinarith
    have h7 : |x 1 - y 1| ^ 2 ≤ δ ^ 2 := by
      have h8 : |x 1 - y 1| ≤ δ := by linarith [h1 1]
      have h9 : 0 ≤ |x 1 - y 1| := by positivity
      nlinarith
    linarith
  have h10 : (Real.sqrt 2 * δ) ^ 2 = 2 * δ ^ 2 := by
    calc (Real.sqrt 2 * δ) ^ 2
      = (Real.sqrt 2) ^ 2 * δ ^ 2 := by ring
    _ = 2 * δ ^ 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
  have h11 : 0 ≤ ‖x - y‖ := by positivity
  have h12 : 0 ≤ Real.sqrt 2 * δ := by positivity
  nlinarith

/-- Convert a bounded 2D S-set of tube parameters Tz at point z (with approximate
incidence ≤ δ/2) into a family of appendix dyadic tubes with exact incidence.
The resulting tube family has controlled SC-set property and encard. -/
lemma parameterSet_to_tubeFamily {δ : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {s C : ℝ} (hs : 0 < s) (hs1 : s < 1) (hC : 0 < C)
    (z : EuclideanSpace ℝ (Fin 2))
    (Tz : Set (ℝ × ℝ))
    (hTz_bdd : Bornology.IsBounded Tz)
    (hTz_nonempty : Tz.Nonempty)
    (hTz : IsDeltaSSet δ s C Tz)
    (h_inc : ∀ (p : ℝ × ℝ), p ∈ Tz →
       |p.1 * (z 1) + p.2 - (z 0)| ≤ δ / 2)
    (hz_bounds : 0 ≤ z 0 ∧ z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1)
    (hTz_bounds : ∀ p ∈ Tz, -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2) :
    ∃ (𝒯z : Set (Set (EuclideanSpace ℝ (Fin 2)))),
      𝒯z ⊆ appendixDyadicTubes δ ∧
      IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s (C * 1000) 𝒯z ∧
      (∀ T ∈ 𝒯z, z ∈ T) ∧
      ENat.toENNReal 𝒯z.encard ≥
        (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) / 1000 ∧
      productLikeAppendixDyadicTubeParameterSet δ 𝒯z ⊆
        Metric.cthickening (Real.sqrt 2 * (3 * δ / 2))
          ((fun p : ℝ × ℝ => WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p.1 else p.2)) '' Tz) :=
by
  classical

  let e : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun p =>
    WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p.1 else p.2)
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, z 0 - p.1 * z 1)

  have hf_move : ∀ p ∈ Tz, dist p (f p) ≤ δ / 2 := by
    intro p hp
    have h : |p.1 * (z 1) + p.2 - (z 0)| ≤ δ / 2 := h_inc p hp
    have h2 : dist p (f p) = |p.2 - (z 0 - p.1 * (z 1))| := by
      have h21 : (f p).1 = p.1 := by simp [f]
      have h22 : (f p).2 = z 0 - p.1 * (z 1) := by simp [f]
      have h_dist : dist p (f p) = max (|p.1 - (f p).1|) (|p.2 - (f p).2|) := by
        simp [Prod.dist_eq, dist_eq_norm] <;> rfl
      rw [h_dist, h21, h22]
      have h_zero : |p.1 - p.1| = 0 := by simp
      rw [h_zero]
      simp [max_eq_right] <;> exact abs_nonneg _
    rw [h2]
    have h3 : |p.2 - (z 0 - p.1 * (z 1))| = |p.1 * (z 1) + p.2 - (z 0)| := by
      have h4 : p.2 - (z 0 - p.1 * (z 1)) = p.1 * (z 1) + p.2 - (z 0) := by ring
      rw [h4]
    rw [h3]; exact h

  have hf_strip : ∀ p ∈ Tz, e (f p) ∈ appendixParameterStrip := by
    intro p hp
    have h1 : -1 ≤ p.1 := (hTz_bounds p hp).1
    have h1' : p.1 ≤ 1 := (hTz_bounds p hp).2.1
    have h_eq0 : (e (f p)) 0 = p.1 := by simp [e, f] <;> ring
    simp only [appendixParameterStrip, Set.mem_setOf_eq]
    rw [h_eq0]
    exact ⟨h1, h1'⟩

  let k_p : ℝ × ℝ → (Fin 2 → ℤ) := fun p =>
    Classical.choose (exists_dyadicCube2 hδ (e (f p)))
  have hk_p : ∀ p, e (f p) ∈ dyadicCube δ (k_p p) := by
    intro p
    exact Classical.choose_spec (exists_dyadicCube2 hδ (e (f p)))

  let Indices : Set (Fin 2 → ℤ) := {k | ∃ p ∈ Tz, k = k_p p}
  let Cubes' : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    {P | ∃ k ∈ Indices, P = dyadicCube δ k}
  let 𝒯z : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    appendixDualOfParameterSet '' Cubes'

  have h_cubes_strip : ∀ P ∈ Cubes', P ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip := by
    intro P hP
    rcases hP with ⟨k, hk, rfl⟩
    rcases hk with ⟨p, hp, rfl⟩
    have h1 : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
    have h2 : e (f p) ∈ appendixParameterStrip := hf_strip p hp
    exact ⟨by exact ⟨k_p p, rfl⟩, ⟨e (f p), h1, h2⟩⟩

  have h1 : 𝒯z ⊆ appendixDyadicTubes δ := by
    intro T hT
    rcases hT with ⟨P, hP, rfl⟩
    exact ⟨P, h_cubes_strip P hP, rfl⟩

  have h2 : ∀ T ∈ 𝒯z, z ∈ T := by
    intro T hT
    rcases hT with ⟨P, hP, rfl⟩
    rcases hP with ⟨k, hk, rfl⟩
    rcases hk with ⟨p, hp, rfl⟩
    have h3 : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
    have h4 : z ∈ appendixDualLineMap (e (f p)) := by
      simp only [appendixDualLineMap, Set.mem_setOf_eq, appendixDualLine]
      have h5 : (e (f p)) 0 = p.1 := by simp [e, f] <;> ring
      have h6 : (e (f p)) 1 = z 0 - p.1 * (z 1) := by simp [e, f] <;> ring
      rw [h5, h6] <;> ring
    exact ⟨e (f p), h3, h4⟩

  have h_canonical : ∀ P ∈ Cubes',
      productLikeAppendixDyadicTubeCanonicalParameterCube δ (appendixDualOfParameterSet P) = P := by
    intro P hP
    rcases hP with ⟨k, hk, rfl⟩
    exact canonicalCube_equals_original hδ (h_cubes_strip (dyadicCube δ k) (by exact ⟨k, hk, rfl⟩))

  let P_union := productLikeAppendixDyadicTubeParameterSet δ 𝒯z

  have h_img : (productLikeAppendixDyadicTubeCanonicalParameterCube δ '' 𝒯z) = Cubes' := by
    apply Set.ext
    intro P
    constructor
    · rintro ⟨T, hT, rfl⟩
      rcases hT with ⟨P', hP', rfl⟩
      have h_eq : productLikeAppendixDyadicTubeCanonicalParameterCube δ (appendixDualOfParameterSet P') = P' :=
        h_canonical P' hP'
      rw [h_eq]
      exact hP'
    · intro hP
      refine ⟨appendixDualOfParameterSet P, ?_, ?_⟩
      · exact ⟨P, hP, rfl⟩
      · exact h_canonical P hP

  have hP_union_eq : P_union = Set.sUnion Cubes' := by
    have h_unfold : P_union = Set.sUnion (productLikeAppendixDyadicTubeCanonicalParameterCube δ '' 𝒯z) := by rfl
    rw [h_unfold, h_img] <;> rfl

  have h_e_lip : LipschitzWith ⟨Real.sqrt 2, by positivity⟩ e := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h2 : ‖e p - e q‖ ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
      simp [e, EuclideanSpace.real_norm_sq_eq] <;> ring
    have h3 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by
      simp [Prod.dist_eq, dist_eq_norm] <;> rfl
    have h4 : ‖e p - e q‖ ≤ Real.sqrt 2 * dist p q := by
      have h6 : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 2 * (dist p q) ^ 2 := by
        rw [h3]
        let m := max (|p.1 - q.1|) (|p.2 - q.2|)
        have h7 : |p.1 - q.1| ≤ m := le_max_left _ _
        have h8 : |p.2 - q.2| ≤ m := le_max_right _ _
        have h9 : (p.1 - q.1) ^ 2 ≤ m ^ 2 := by
          have h10 : |p.1 - q.1| ^ 2 ≤ m ^ 2 := by gcongr
          have h11 : (p.1 - q.1) ^ 2 = |p.1 - q.1| ^ 2 := by rw [sq_abs]
          rw [h11]; exact h10
        have h12 : (p.2 - q.2) ^ 2 ≤ m ^ 2 := by
          have h13 : |p.2 - q.2| ^ 2 ≤ m ^ 2 := by gcongr
          have h14 : (p.2 - q.2) ^ 2 = |p.2 - q.2| ^ 2 := by rw [sq_abs]
          rw [h14]; exact h13
        linarith
      have h9 : (Real.sqrt 2 * dist p q) ^ 2 = 2 * (dist p q) ^ 2 := by
        calc (Real.sqrt 2 * dist p q) ^ 2
          = (Real.sqrt 2) ^ 2 * (dist p q) ^ 2 := by ring
        _ = 2 * (dist p q) ^ 2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
      have h5 : ‖e p - e q‖ ^ 2 ≤ (Real.sqrt 2 * dist p q) ^ 2 := by
        rw [h2, h9]; exact h6
      have h10 : 0 ≤ ‖e p - e q‖ := by positivity
      have h11 : 0 ≤ Real.sqrt 2 * dist p q := by positivity
      nlinarith
    exact h4

  have h_f_lip : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have hz1 : 0 ≤ z 1 := hz_bounds.2.2.1
    have hz2 : z 1 ≤ 1 := hz_bounds.2.2.2
    have h_abs : |z 1| ≤ 1 := by
      rw [abs_of_nonneg hz1] <;> linarith
    have h1 : dist (f p) (f q) = max (|p.1 - q.1|) (|z 1| * |p.1 - q.1|) := by
      have h2 : (f p).2 - (f q).2 = -((p.1 - q.1) * z 1) := by
        simp [f] <;> ring
      simp [f, Prod.dist_eq, dist_eq_norm, h2, abs_mul, abs_neg] <;> ring_nf
    rw [h1]
    have h4 : |z 1| * |p.1 - q.1| ≤ |p.1 - q.1| := by
      have h5 : |z 1| ≤ 1 := h_abs
      have h6 : 0 ≤ |p.1 - q.1| := by positivity
      nlinarith
    have h7 : |p.1 - q.1| ≤ dist p q := by
      simp [Prod.dist_eq, dist_eq_norm] <;> exact le_max_left _ _
    have h8 : |z 1| * |p.1 - q.1| ≤ dist p q := by linarith
    have h9 : max (|p.1 - q.1|) (|z 1| * |p.1 - q.1|) ≤ dist p q := max_le h7 h8
    simpa using h9

  have h_f_lip' : LipschitzWith (⟨1, by norm_num⟩ : NNReal) f := h_f_lip
  have h_image_eq : (e ∘ f) '' Tz = e '' (f '' Tz) := by
    rw [← Set.image_comp]
  have h_ef_bdd : Bornology.IsBounded ((e ∘ f) '' Tz) := by
    rw [h_image_eq]
    exact h_e_lip.isBounded_image (h_f_lip'.isBounded_image hTz_bdd)
  have h_cube_bdd : ∀ (k : Fin 2 → ℤ), Bornology.IsBounded (dyadicCube δ k) :=
    fun k => dyadicCube_bounded hδ

  have h_indices_sub : Indices ⊆ {k : Fin 2 → ℤ | (dyadicCube δ k ∩ (e ∘ f) '' Tz).Nonempty} := by
    intro k hk
    rcases hk with ⟨p, hp, rfl⟩
    have h1 : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
    have h2 : e (f p) ∈ (e ∘ f) '' Tz := ⟨p, hp, rfl⟩
    exact ⟨e (f p), h1, h2⟩
  have h_indices_fin : Set.Finite Indices :=
    Set.Finite.subset (finite_dyadicCubes_meeting_bounded hδ h_ef_bdd) h_indices_sub
  have h_cubes_fin : Set.Finite Cubes' := by
    have h_eq : Cubes' = (fun k : Fin 2 → ℤ => dyadicCube δ k) '' Indices := by
      ext P
      simp only [Cubes', Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨k, hk, h_eq⟩
        exact ⟨k, hk, h_eq.symm⟩
      · rintro ⟨k, hk, h_eq⟩
        exact ⟨k, hk, h_eq.symm⟩
    rw [h_eq]
    exact h_indices_fin.image _

  have h5 : Bornology.IsBounded P_union := by
    rw [hP_union_eq]
    have h_each_bdd : ∀ P ∈ Cubes', Bornology.IsBounded P := by
      intro P hP
      rcases hP with ⟨k, _, rfl⟩
      exact h_cube_bdd k
    have h_main : Bornology.IsBounded (Set.sUnion Cubes') :=
      (Bornology.isBounded_sUnion h_cubes_fin).mpr h_each_bdd
    exact h_main

  have h6 : P_union.Nonempty := by
    rcases hTz_nonempty with ⟨p, hp⟩
    rw [hP_union_eq]
    refine ⟨e (f p), ?_⟩
    have h7 : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
    exact Set.mem_sUnion.mpr ⟨dyadicCube δ (k_p p), by exact ⟨k_p p, ⟨p, hp, rfl⟩, rfl⟩, h7⟩

  -- ===== Encard equality =====
  have h_inj_k : Function.Injective (fun k : Fin 2 → ℤ => dyadicCube δ k) := by
    intro k1 k2 h
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => δ * (k1 i : ℝ) + δ / 2)
    have hx : x ∈ dyadicCube δ k1 := by
      intro i
      have h1 : δ * (k1 i : ℝ) ≤ δ * (k1 i : ℝ) + δ / 2 := by linarith [hδ]
      have h2 : δ * (k1 i : ℝ) + δ / 2 < δ * ((k1 i : ℝ) + 1) := by linarith [hδ]
      exact ⟨h1, h2⟩
    have h_eq_cube : dyadicCube δ k1 = dyadicCube δ k2 := h
    have hx2 : x ∈ dyadicCube δ k2 := by
      exact h_eq_cube ▸ hx
    exact dyadicCube_inter_eq hδ ⟨x, hx, hx2⟩

  have h_cubes_eq1 : Cubes' = (fun k : Fin 2 → ℤ => dyadicCube δ k) '' Indices := by
    ext P; simp [Cubes'] <;> tauto
  have h_cubes_encard : Cubes'.encard = Indices.encard := by
    rw [h_cubes_eq1]
    have h_inj_on : Set.InjOn (fun k : Fin 2 → ℤ => dyadicCube δ k) Indices :=
      fun k1 _ k2 _ h => h_inj_k h
    exact Function.Injective.encard_image h_inj_k Indices
  have h_inj_dual : Set.InjOn appendixDualOfParameterSet Cubes' := by
    intro P1 hP1 P2 hP2 h
    rcases hP1 with ⟨k1, _, rfl⟩
    rcases hP2 with ⟨k2, _, rfl⟩
    have h_k : k1 = k2 := appendixDualOfParameterSet_injective_on_dyadicCubes δ hδ (by simp) (by simp) h
    rw [h_k]
  have h_tube_encard : 𝒯z.encard = Cubes'.encard := by
    rw [show 𝒯z = appendixDualOfParameterSet '' Cubes' from rfl]
    exact Set.InjOn.encard_image h_inj_dual
  have h_encard_eq : 𝒯z.encard = Indices.encard := by
    rw [h_tube_encard, h_cubes_encard]

  -- ===== Representatives =====
  let rep : (Fin 2 → ℤ) → ℝ × ℝ := fun k =>
    if h : k ∈ Indices then Classical.choose h else (0, 0)
  have hrep1 : ∀ k ∈ Indices, rep k ∈ Tz := by
    intro k hk
    have h_eq : rep k = Classical.choose hk := by
      simp [rep, hk, dif_pos hk]
    rw [h_eq]
    exact (Classical.choose_spec hk).1
  have hrep2 : ∀ k ∈ Indices, k_p (rep k) = k := by
    intro k hk
    have h_eq : rep k = Classical.choose hk := by
      simp [rep, hk, dif_pos hk]
    rw [h_eq]
    exact (Classical.choose_spec hk).2.symm

  -- ===== Fiber diameter bound =====
  have h_fiber : ∀ (p : ℝ × ℝ), p ∈ Tz →
      |p.1 - (rep (k_p p)).1| < δ ∧ |p.2 - (rep (k_p p)).2| ≤ 2 * δ := by
    intro p hp
    let k := k_p p
    have hk : k ∈ Indices := ⟨p, hp, rfl⟩
    have h1 : e (f p) ∈ dyadicCube δ k := hk_p p
    have h21 : e (f (rep k)) ∈ dyadicCube δ (k_p (rep k)) := hk_p (rep k)
    have h22 : k_p (rep k) = k := hrep2 k hk
    have h2 : e (f (rep k)) ∈ dyadicCube δ k := by simpa [h22] using h21
    have h3 : |(e (f p)) 0 - (e (f (rep k))) 0| < δ := by
      have h41 : δ * (k 0 : ℝ) ≤ (e (f p)) 0 := (h1 0).1
      have h42 : (e (f p)) 0 < δ * ((k 0 : ℝ) + 1) := (h1 0).2
      have h51 : δ * (k 0 : ℝ) ≤ (e (f (rep k))) 0 := (h2 0).1
      have h52 : (e (f (rep k))) 0 < δ * ((k 0 : ℝ) + 1) := (h2 0).2
      have h_goal1 : (e (f p)) 0 - (e (f (rep k))) 0 < δ := by
        set a : ℝ := (e (f p)) 0 with ha
        set b : ℝ := (e (f (rep k))) 0 with hb
        set k0 : ℝ := (k 0 : ℝ) with hk0
        have h41' : δ * k0 ≤ a := by simpa [ha, hk0] using h41
        have h42' : a < δ * (k0 + 1) := by simpa [ha, hk0] using h42
        have h51' : δ * k0 ≤ b := by simpa [hb, hk0] using h51
        have h52' : b < δ * (k0 + 1) := by simpa [hb, hk0] using h52
        linarith
      have h_goal2 : (e (f (rep k))) 0 - (e (f p)) 0 < δ := by
        set a : ℝ := (e (f p)) 0 with ha
        set b : ℝ := (e (f (rep k))) 0 with hb
        set k0 : ℝ := (k 0 : ℝ) with hk0
        have h41' : δ * k0 ≤ a := by simpa [ha, hk0] using h41
        have h42' : a < δ * (k0 + 1) := by simpa [ha, hk0] using h42
        have h51' : δ * k0 ≤ b := by simpa [hb, hk0] using h51
        have h52' : b < δ * (k0 + 1) := by simpa [hb, hk0] using h52
        linarith
      rw [abs_sub_lt_iff]
      exact ⟨h_goal1, h_goal2⟩
    have h4 : |(e (f p)) 1 - (e (f (rep k))) 1| < δ := by
      have h41 : δ * (k 1 : ℝ) ≤ (e (f p)) 1 := (h1 1).1
      have h42 : (e (f p)) 1 < δ * ((k 1 : ℝ) + 1) := (h1 1).2
      have h51 : δ * (k 1 : ℝ) ≤ (e (f (rep k))) 1 := (h2 1).1
      have h52 : (e (f (rep k))) 1 < δ * ((k 1 : ℝ) + 1) := (h2 1).2
      have h_goal1 : (e (f p)) 1 - (e (f (rep k))) 1 < δ := by
        set a : ℝ := (e (f p)) 1 with ha
        set b : ℝ := (e (f (rep k))) 1 with hb
        set k1 : ℝ := (k 1 : ℝ) with hk1
        have h41' : δ * k1 ≤ a := by simpa [ha, hk1] using h41
        have h42' : a < δ * (k1 + 1) := by simpa [ha, hk1] using h42
        have h51' : δ * k1 ≤ b := by simpa [hb, hk1] using h51
        have h52' : b < δ * (k1 + 1) := by simpa [hb, hk1] using h52
        linarith
      have h_goal2 : (e (f (rep k))) 1 - (e (f p)) 1 < δ := by
        set a : ℝ := (e (f p)) 1 with ha
        set b : ℝ := (e (f (rep k))) 1 with hb
        set k1 : ℝ := (k 1 : ℝ) with hk1
        have h41' : δ * k1 ≤ a := by simpa [ha, hk1] using h41
        have h42' : a < δ * (k1 + 1) := by simpa [ha, hk1] using h42
        have h51' : δ * k1 ≤ b := by simpa [hb, hk1] using h51
        have h52' : b < δ * (k1 + 1) := by simpa [hb, hk1] using h52
        linarith
      rw [abs_sub_lt_iff]
      exact ⟨h_goal1, h_goal2⟩
    have h5 : (e (f p)) 0 = p.1 := by simp [e, f] <;> ring
    have h6 : (e (f (rep k))) 0 = (rep k).1 := by simp [e, f] <;> ring
    have h7 : (e (f p)) 1 = (f p).2 := by simp [e, f] <;> ring
    have h8 : (e (f (rep k))) 1 = (f (rep k)).2 := by simp [e, f] <;> ring
    have h9 : |p.1 - (rep k).1| < δ := by rw [←h5, ←h6]; exact h3
    have h10 : |(f p).2 - (f (rep k)).2| < δ := by rw [←h7, ←h8]; exact h4
    have h11 : |p.2 - (f p).2| ≤ δ / 2 := by
      have h : |p.2 - (f p).2| ≤ dist p (f p) := by
        simp [Prod.dist_eq, dist_eq_norm] <;> exact le_max_right _ _
      exact h.trans (hf_move p hp)
    have h12 : |(rep k).2 - (f (rep k)).2| ≤ δ / 2 := by
      have h : |(rep k).2 - (f (rep k)).2| ≤ dist (rep k) (f (rep k)) := by
        simp [Prod.dist_eq, dist_eq_norm] <;> exact le_max_right _ _
      exact h.trans (hf_move (rep k) (hrep1 k hk))
    have h13 : |p.2 - (rep k).2| ≤ 2 * δ := by
      have h14 : |p.2 - (rep k).2| ≤ |p.2 - (f p).2| + |(f p).2 - (rep k).2| := by exact abs_sub_le p.2 (f p).2 (rep k).2
      have h15 : |(f p).2 - (rep k).2| ≤ |(f p).2 - (f (rep k)).2| + |(f (rep k)).2 - (rep k).2| := by exact abs_sub_le (f p).2 (f (rep k)).2 (rep k).2
      have h16 : |(f (rep k)).2 - (rep k).2| = |(rep k).2 - (f (rep k)).2| := by rw [abs_sub_comm]
      rw [h16] at h15
      linarith [h10.le, h11, h12, h14, h15]
    exact ⟨h9, h13⟩

  -- ===== Cover Tz by 2 δ-balls per index =====
  let c_plus : (Fin 2 → ℤ) → ℝ × ℝ := fun k => ((rep k).1, (rep k).2 + δ)
  let c_minus : (Fin 2 → ℤ) → ℝ × ℝ := fun k => ((rep k).1, (rep k).2 - δ)
  let Centers : Set (ℝ × ℝ) := c_plus '' Indices ∪ c_minus '' Indices

  have h_centers_encard : Centers.encard ≤ 2 * Indices.encard := by
    have h1 : (c_plus '' Indices).encard ≤ Indices.encard := Set.encard_image_le _ _
    have h2 : (c_minus '' Indices).encard ≤ Indices.encard := Set.encard_image_le _ _
    have h3 : Centers.encard ≤ (c_plus '' Indices).encard + (c_minus '' Indices).encard :=
      Set.encard_union_le _ _
    calc Centers.encard
      ≤ (c_plus '' Indices).encard + (c_minus '' Indices).encard := h3
    _ ≤ Indices.encard + Indices.encard := by gcongr
    _ = 2 * Indices.encard := by ring

  have h_is_cover : Metric.IsCover δ.toNNReal Tz Centers := by
    intro x hx
    let k := k_p x
    have hk : k ∈ Indices := ⟨x, hx, rfl⟩
    have h_fib : |x.1 - (rep k).1| < δ ∧ |x.2 - (rep k).2| ≤ 2 * δ := by
      simpa [k] using h_fiber x hx
    by_cases h_case : x.2 ≥ (rep k).2
    · have h16 : |x.2 - ((rep k).2 + δ)| ≤ δ := by
        have h17 : 0 ≤ x.2 - (rep k).2 := by linarith
        have h18 : x.2 - (rep k).2 ≤ 2 * δ := (abs_le.mp h_fib.2).2
        have h19 : |x.2 - ((rep k).2 + δ)| = |x.2 - (rep k).2 - δ| := by ring_nf
        rw [h19, abs_le] <;> constructor <;> linarith
      have h20 : |x.1 - (rep k).1| ≤ δ := h_fib.1.le
      have h21 : dist x (c_plus k) ≤ δ := by
        simp [c_plus, Prod.dist_eq, dist_eq_norm, h20, h16] <;> exact max_le h20 h16
      have hc : c_plus k ∈ Centers := Set.mem_union_left _ (Set.mem_image_of_mem _ hk)
      have h0 : 0 ≤ δ := by linarith
      have h_edist : edist x (c_plus k) ≤ ↑δ.toNNReal := by
        have h_eq : ENNReal.ofReal δ = ↑δ.toNNReal := by
          simp [ENNReal.ofReal, h0] <;> rfl
        have h : edist x (c_plus k) ≤ ENNReal.ofReal δ := by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal h21
        rw [h_eq] at h
        exact h
      exact ⟨c_plus k, hc, h_edist⟩
    · have h_case' : x.2 < (rep k).2 := by linarith
      have h17 : -(2 * δ) ≤ x.2 - (rep k).2 := (abs_le.mp h_fib.2).1
      have h17' : -2 * δ ≤ x.2 - (rep k).2 := by ring_nf at h17 ⊢; exact h17
      have h16 : |x.2 - ((rep k).2 - δ)| ≤ δ := by
        have h18 : x.2 - (rep k).2 < 0 := by linarith
        have h19 : |x.2 - ((rep k).2 - δ)| = |x.2 - (rep k).2 + δ| := by ring_nf
        rw [h19]
        have h20 : -δ ≤ x.2 - (rep k).2 + δ := by linarith
        have h21 : x.2 - (rep k).2 + δ ≤ δ := by linarith
        exact abs_le.mpr ⟨h20, h21⟩
      have h20 : |x.1 - (rep k).1| ≤ δ := h_fib.1.le
      have h21 : dist x (c_minus k) ≤ δ := by
        simp [c_minus, Prod.dist_eq, dist_eq_norm, h20, h16] <;> exact max_le h20 h16
      have hc : c_minus k ∈ Centers := Set.mem_union_right _ (Set.mem_image_of_mem _ hk)
      have h0 : 0 ≤ δ := by linarith
      have h_edist : edist x (c_minus k) ≤ ↑δ.toNNReal := by
        have h_eq : ENNReal.ofReal δ = ↑δ.toNNReal := by
          simp [ENNReal.ofReal, h0] <;> rfl
        have h : edist x (c_minus k) ≤ ENNReal.ofReal δ := by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal h21
        rw [h_eq] at h
        exact h
      exact ⟨c_minus k, hc, h_edist⟩

  have h_ext_le : Metric.externalCoveringNumber δ.toNNReal Tz ≤ Centers.encard :=
    h_is_cover.externalCoveringNumber_le_encard

  have h_covering_le : (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) ≤ 2 * ENat.toENNReal Indices.encard := by
    have h5 : (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) ≤ ENat.toENNReal Centers.encard := by
      exact_mod_cast h_ext_le
    have h6 : ENat.toENNReal Centers.encard ≤ 2 * ENat.toENNReal Indices.encard := by
      exact_mod_cast h_centers_encard
    exact h5.trans h6

  -- ===== Encard lower bound =====
  have h_encard_lower : ENat.toENNReal 𝒯z.encard ≥ (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) / 1000 := by
    rw [h_encard_eq]
    have h6 : (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) ≤ ENat.toENNReal Indices.encard * 1000 := by
      calc (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal)
        ≤ 2 * ENat.toENNReal Indices.encard := h_covering_le
      _ = ENat.toENNReal Indices.encard * 2 := by ring
      _ ≤ ENat.toENNReal Indices.encard * 1000 := by gcongr <;> norm_num
    have h9 : (1000 : ENNReal) ≠ 0 := by norm_num
    have h10 : (1000 : ENNReal) ≠ ⊤ := by norm_num
    have h8 : (Metric.externalCoveringNumber δ.toNNReal Tz : ENNReal) / 1000 ≤ ENat.toENNReal Indices.encard := by
      rw [ENNReal.div_le_iff h9 h10]
      exact h6
    exact h8

  -- ===== dyadicCoveringNumber equalities =====
  have h_dyadic_union : dyadicCubesMeeting δ P_union = Cubes' := by
    apply Set.ext
    intro P
    simp only [dyadicCubesMeeting, Cubes', Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP_cubes, h_inter⟩
      rcases hP_cubes with ⟨k, rfl⟩
      rcases h_inter with ⟨x, hx_P, hx_union⟩
      have h_xin : x ∈ Set.sUnion Cubes' := by rw [←hP_union_eq]; exact hx_union
      rcases Set.mem_sUnion.mp h_xin with ⟨P', hP'_in, hx_P'⟩
      rcases hP'_in with ⟨k', hk', rfl⟩
      have h_k_eq : k = k' := dyadicCube_inter_eq hδ ⟨x, hx_P, hx_P'⟩
      rw [h_k_eq] at *
      exact ⟨k', hk', rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases hk with ⟨p, hp, rfl⟩
      have h1 : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
      have h2 : e (f p) ∈ P_union := by
        rw [hP_union_eq]
        exact Set.mem_sUnion.mpr ⟨dyadicCube δ (k_p p), by exact ⟨k_p p, ⟨p, hp, rfl⟩, rfl⟩, h1⟩
      exact ⟨by exact ⟨k_p p, rfl⟩, ⟨e (f p), h1, h2⟩⟩

  have h_dyadic_cover_eq : (dyadicCoveringNumber δ P_union : ENat) = Indices.encard := by
    rw [dyadicCoveringNumber, h_dyadic_union, h_cubes_encard]

  -- ===== SC-set property =====
  have h_s_nonneg : 0 ≤ s := by linarith [hs]
  have h_s_le_two : s ≤ (2 : ℝ) := by linarith [hs1]
  have h_C1000_pos : 0 < C * 1000 := by positivity

  have h_sc_main : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 2))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 2 r → δ ≤ r → r ≤ 1 →
        ENat.toENNReal (dyadicCoveringNumber (d := 2) δ (P_union ∩ Q)) ≤
          ENNReal.ofReal (C * 1000) * ENat.toENNReal (dyadicCoveringNumber (d := 2) δ P_union) *
            ENNReal.ofReal (r ^ s) := by
    intro r Q hr_dyadic hQ_cubes hδ_le_r hr_le_one
    have h_r_pos : 0 < r := by
      rcases hr_dyadic with ⟨n, rfl⟩
      positivity
    rcases hQ_cubes with ⟨k_Q, rfl⟩
    let c_Q : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => r * ((k_Q i : ℝ) + 1 / 2))
    let c_Q' : ℝ × ℝ := (c_Q 0, c_Q 1)
    let K_Q : Set (Fin 2 → ℤ) := {k ∈ Indices | (dyadicCube δ k ∩ dyadicCube r k_Q).Nonempty}

    have hKQ_fin : Set.Finite K_Q := Set.Finite.subset h_indices_fin (fun k hk => hk.1)
    have hKQ_sub : K_Q ⊆ Indices := fun k hk => hk.1

    have h_rep_in_ball : ∀ k ∈ K_Q, rep k ∈ Metric.closedBall c_Q' (2 * r) := by
      intro k hk
      have hkin : k ∈ Indices := hk.1
      have h_inter : (dyadicCube δ k ∩ dyadicCube r k_Q).Nonempty := hk.2
      rcases h_inter with ⟨y, hy_cube, hy_Q⟩
      have h_ef1 : e (f (rep k)) ∈ dyadicCube δ (k_p (rep k)) := hk_p (rep k)
      have h_ef2 : k_p (rep k) = k := hrep2 k hkin
      have h_ef : e (f (rep k)) ∈ dyadicCube δ k := by simpa [h_ef2] using h_ef1
      have h1 : ∀ i : Fin 2, |(e (f (rep k))) i - y i| < δ := by
        intro i
        have h41 : δ * (k i : ℝ) ≤ (e (f (rep k))) i := (h_ef i).1
        have h42 : (e (f (rep k))) i < δ * ((k i : ℝ) + 1) := (h_ef i).2
        have h51 : δ * (k i : ℝ) ≤ y i := (hy_cube i).1
        have h52 : y i < δ * ((k i : ℝ) + 1) := (hy_cube i).2
        rw [abs_sub_lt_iff] <;> constructor <;> linarith
      have h2 : ∀ i : Fin 2, |y i - c_Q i| ≤ r / 2 := by
        intro i
        have h3 : y i ∈ Set.Ico (r * (k_Q i : ℝ)) (r * ((k_Q i : ℝ) + 1)) := hy_Q i
        have h41 : r * (k_Q i : ℝ) ≤ y i := h3.1
        have h42 : y i < r * ((k_Q i : ℝ) + 1) := h3.2
        have h51 : -(r / 2) ≤ y i - r * ((k_Q i : ℝ) + 1 / 2) := by linarith
        have h52 : y i - r * ((k_Q i : ℝ) + 1 / 2) ≤ r / 2 := by linarith
        exact abs_le.mpr ⟨h51, h52⟩
      have h3 : |(rep k).1 - c_Q 0| < δ + r / 2 := by
        have h4 : (e (f (rep k))) 0 = (rep k).1 := by simp [e, f] <;> ring
        rw [←h4]
        calc |(e (f (rep k))) 0 - c_Q 0|
          ≤ |(e (f (rep k))) 0 - y 0| + |y 0 - c_Q 0| := by exact abs_sub_le ((e (f (rep k))).ofLp 0) (y.ofLp 0) (c_Q.ofLp 0)
        _ < δ + r / 2 := by linarith [h1 0, h2 0]
      have h4 : |(f (rep k)).2 - c_Q 1| < δ + r / 2 := by
        have h5 : (e (f (rep k))) 1 = (f (rep k)).2 := by simp [e, f] <;> ring
        rw [←h5]
        calc |(e (f (rep k))) 1 - c_Q 1|
          ≤ |(e (f (rep k))) 1 - y 1| + |y 1 - c_Q 1| := by exact abs_sub_le ((e (f (rep k))).ofLp 1) (y.ofLp 1) (c_Q.ofLp 1)
        _ < δ + r / 2 := by linarith [h1 1, h2 1]
      have h5 : |(rep k).2 - (f (rep k)).2| ≤ δ / 2 := by
        have h : |(rep k).2 - (f (rep k)).2| ≤ dist (rep k) (f (rep k)) := by
          simp [Prod.dist_eq, dist_eq_norm] <;> exact le_max_right _ _
        exact h.trans (hf_move (rep k) (hrep1 k hkin))
      have h6 : |(rep k).2 - c_Q 1| ≤ 3 * δ / 2 + r / 2 := by
        calc |(rep k).2 - c_Q 1|
          ≤ |(rep k).2 - (f (rep k)).2| + |(f (rep k)).2 - c_Q 1| := by exact abs_sub_le (rep k).2 (f (rep k)).2 (c_Q.ofLp 1)
        _ ≤ δ / 2 + (δ + r / 2) := by gcongr <;> linarith
        _ = 3 * δ / 2 + r / 2 := by ring
      have h7 : δ + r / 2 ≤ 2 * r := by linarith [hδ_le_r, h_r_pos]
      have h8 : 3 * δ / 2 + r / 2 ≤ 2 * r := by linarith [hδ_le_r, h_r_pos]
      have h9 : |(rep k).1 - c_Q 0| ≤ 2 * r := by linarith
      have h10 : |(rep k).2 - c_Q 1| ≤ 2 * r := by linarith
      have h11 : dist (rep k) c_Q' ≤ 2 * r := by
        simp [c_Q', Prod.dist_eq, dist_eq_norm] <;> exact max_le h9 h10
      exact h11

    have h_dyadic_inter : dyadicCubesMeeting δ (P_union ∩ dyadicCube r k_Q) =
        (fun k : Fin 2 → ℤ => dyadicCube δ k) '' K_Q := by
      apply Set.ext
      intro P
      simp only [dyadicCubesMeeting, K_Q, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨⟨k, rfl⟩, h_inter⟩
        rcases h_inter with ⟨x, hx_P, hx_inter⟩
        have h_xin_union : x ∈ P_union := hx_inter.1
        have h_xin_Q : x ∈ dyadicCube r k_Q := hx_inter.2
        have h_xin_cube : x ∈ dyadicCube δ k := hx_P
        have h_xin_sunion : x ∈ Set.sUnion Cubes' := by rw [←hP_union_eq]; exact h_xin_union
        rcases Set.mem_sUnion.mp h_xin_sunion with ⟨P', hP'_in, hx_P'⟩
        rcases hP'_in with ⟨k', hk', rfl⟩
        have h_k_eq : k = k' := dyadicCube_inter_eq hδ ⟨x, hx_P, hx_P'⟩
        rw [h_k_eq] at *
        refine ⟨k', ⟨hk', ⟨x, hx_P', h_xin_Q⟩⟩, rfl⟩
      · rintro ⟨k, ⟨hkin, h_inter⟩, rfl⟩
        have h1 : dyadicCube δ k ⊆ P_union := by
          intro x hx
          rw [hP_union_eq]
          exact Set.mem_sUnion.mpr ⟨dyadicCube δ k, ⟨k, hkin, rfl⟩, hx⟩
        rcases h_inter with ⟨x, hx_cube, hx_Q⟩
        exact ⟨⟨k, rfl⟩, ⟨x, hx_cube, h1 hx_cube, hx_Q⟩⟩

    have h_KQ_encard : (dyadicCoveringNumber δ (P_union ∩ dyadicCube r k_Q) : ENat) = K_Q.encard := by
      rw [dyadicCoveringNumber, h_dyadic_inter]
      have h_inj : Set.InjOn (fun k : Fin 2 → ℤ => dyadicCube δ k) K_Q := by
        intro k1 _ k2 _ h
        exact h_inj_k h
      exact Function.Injective.encard_image h_inj_k K_Q

    let A_cover := Tz ∩ Metric.closedBall c_Q' (2 * r)
    have hA_bdd : Bornology.IsBounded A_cover := by
      have h : A_cover ⊆ Tz := by
        simpa [A_cover] using Set.inter_subset_left
      exact Bornology.IsBounded.subset hTz_bdd h
    have hε_pos : 0 < δ.toNNReal := by positivity
    have h_fin : Metric.externalCoveringNumber δ.toNNReal A_cover < ⊤ :=
      externalCoveringNumber_bounded_prod hε_pos hA_bdd
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_fin with ⟨t₀, ht₀_cover, ht₀_eq⟩
    have h_le_sInf' : ENat.toENNReal K_Q.encard ≤ (49 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A_cover : ENNReal) := by
      have h_main := kq_encard_bound hδ hKQ_fin hKQ_sub hrep1 hrep2 (fun p _ => hk_p p) h_f_lip h_e_lip h_rep_in_ball ht₀_cover
      rw [ht₀_eq] at h_main
      exact h_main

    have h_2r_ge_delta : δ ≤ 2 * r := by linarith [hδ_le_r]
    have h_sset := hTz.2.2.2.2 c_Q' (2 * r) h_2r_ge_delta

    have h9 : ENat.toENNReal K_Q.encard ≤
        (49 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
          Metric.externalCoveringNumber δ.toNNReal Tz) := by
      calc ENat.toENNReal K_Q.encard
        ≤ (49 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (Tz ∩ Metric.closedBall c_Q' (2 * r)) := h_le_sInf'
      _ ≤ (49 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
            Metric.externalCoveringNumber δ.toNNReal Tz) := by
          gcongr <;> exact h_sset

    have h10 : (ENNReal.ofReal (2 * r)) ^ s = ENNReal.ofReal ((2 * r) ^ s) := by
      have h_pos : 0 ≤ 2 * r := by linarith [h_r_pos]
      exact ENNReal.ofReal_rpow_of_nonneg h_pos h_s_nonneg
    have h11 : (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    rw [h10, h11] at h9
    have h12 : (2 : ℝ) ^ s ≤ 2 := by
      have h13 : s ≤ 1 := by linarith [hs1]
      have h14 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h13
      have h15 : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
      rw [h15] at h14; exact h14
    have h13 : ENNReal.ofReal ((2 : ℝ) ^ s * r ^ s) ≤ ENNReal.ofReal (2 * r ^ s) := by
      have h131 : (2 : ℝ) ^ s * r ^ s ≤ 2 * r ^ s := by
        have h133 : 0 ≤ r ^ s := by positivity
        nlinarith
      exact ENNReal.ofReal_le_ofReal h131
    have h14 : ENat.toENNReal K_Q.encard ≤
        (49 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (2 * r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz) := by
      calc ENat.toENNReal K_Q.encard
        ≤ (49 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ s * r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz) := h9
      _ ≤ (49 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (2 * r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz) := by
          gcongr <;> exact h13
    have h_ofreal2 : ENNReal.ofReal (2 * r ^ s) = (2 : ENNReal) * ENNReal.ofReal (r ^ s) := by
      rw [show (2 * r ^ s : ℝ) = (2 : ℝ) * (r ^ s) by ring]
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_cast
    have h15 : ENat.toENNReal K_Q.encard ≤
        (98 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz := by
      rw [h_ofreal2] at h14
      have h_eq : (49 : ENNReal) * (ENNReal.ofReal C * ((2 : ENNReal) * ENNReal.ofReal (r ^ s)) * Metric.externalCoveringNumber δ.toNNReal Tz) =
          (98 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz := by ring
      rw [h_eq] at h14
      exact h14
    have h16 : ENat.toENNReal K_Q.encard ≤
        (196 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * ENat.toENNReal Indices.encard := by
      calc ENat.toENNReal K_Q.encard
        ≤ (98 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * Metric.externalCoveringNumber δ.toNNReal Tz := h15
      _ ≤ (98 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (2 * ENat.toENNReal Indices.encard) := by
          gcongr <;> exact h_covering_le
      _ = (196 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * ENat.toENNReal Indices.encard := by ring
    have h18 : (196 : ENNReal) * ENNReal.ofReal C ≤ ENNReal.ofReal (C * 1000) := by
      have h19 : (196 : ℝ) * C ≤ C * 1000 := by linarith
      have h20 : ENNReal.ofReal ((196 : ℝ) * C) ≤ ENNReal.ofReal (C * 1000) := ENNReal.ofReal_le_ofReal h19
      have h_C_nonneg : 0 ≤ C := by linarith [hC]
      have h21 : (196 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal ((196 : ℝ) * C) := by
        have h_pos196 : 0 ≤ (196 : ℝ) := by norm_num
        have h22 : ENNReal.ofReal ((196 : ℝ) * C) = ENNReal.ofReal (196 : ℝ) * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul h_pos196] <;> norm_cast
        have h23 : ENNReal.ofReal (196 : ℝ) = (196 : ENNReal) := by norm_cast
        rw [h23] at h22
        exact h22.symm
      rw [h21]; exact h20
    have h19 : (196 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * ENat.toENNReal Indices.encard ≤
        ENNReal.ofReal (C * 1000) * ENNReal.ofReal (r ^ s) * ENat.toENNReal Indices.encard := by
      gcongr <;> exact h18
    have h20 : ENNReal.ofReal (C * 1000) * ENNReal.ofReal (r ^ s) * ENat.toENNReal Indices.encard =
        ENNReal.ofReal (C * 1000) * ENat.toENNReal Indices.encard * ENNReal.ofReal (r ^ s) := by ring
    rw [h_dyadic_cover_eq]
    rw [h_KQ_encard]
    exact h16.trans (h19.trans h20.le)

  have h_sc : IsDeltaSCSet (d := 2) δ s (C * 1000) P_union :=
    ⟨h5, h6, by norm_num, hδ_dyadic, hδ, h_s_nonneg, h_s_le_two, h_C1000_pos, h_sc_main⟩

  have h_product : IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s (C * 1000) 𝒯z :=
    ⟨h1, by linarith [hs], by linarith [hs1], h_sc⟩

  -- ===== Thickening conclusion =====
  have h_thicken : P_union ⊆ Metric.cthickening (Real.sqrt 2 * (3 * δ / 2)) (e '' Tz) := by
    intro x hx
    rw [hP_union_eq] at hx
    rcases Set.mem_sUnion.mp hx with ⟨P, hP, hxP⟩
    rcases hP with ⟨k, hk, rfl⟩
    have h_exists : ∃ (p : ℝ × ℝ), p ∈ Tz ∧ k_p p = k := by
      have h' : ∃ (p : ℝ × ℝ), p ∈ Tz ∧ k = k_p p := by simpa [Indices] using hk
      rcases h' with ⟨p, hp, h_eq⟩
      exact ⟨p, hp, h_eq.symm⟩
    rcases h_exists with ⟨p, hp, hkp_eq⟩
    have h_ef_in : e (f p) ∈ dyadicCube δ k := by
      have h : e (f p) ∈ dyadicCube δ (k_p p) := hk_p p
      rw [hkp_eq] at h
      exact h
    have h_dist1 : ‖x - e (f p)‖ ≤ Real.sqrt 2 * δ :=
      dyadicCube_diameter_bound hδ hxP h_ef_in
    have h_dist2 : ‖e (f p) - e p‖ ≤ Real.sqrt 2 * (δ / 2) := by
      have h := h_e_lip.dist_le_mul (f p) p
      have h_move_p : dist (f p) p ≤ δ / 2 := by
        have h2 : dist p (f p) ≤ δ / 2 := hf_move p hp
        rw [dist_comm] at h2
        exact h2
      calc ‖e (f p) - e p‖
        ≤ Real.sqrt 2 * dist (f p) p := h
      _ ≤ Real.sqrt 2 * (δ / 2) := by gcongr
    have h_eq : x - e p = (x - e (f p)) + (e (f p) - e p) := by abel
    have h_dist3 : ‖x - e p‖ ≤ Real.sqrt 2 * (3 * δ / 2) := by
      rw [h_eq]
      have h_tri : ‖(x - e (f p)) + (e (f p) - e p)‖ ≤ ‖x - e (f p)‖ + ‖e (f p) - e p‖ :=
        norm_add_le _ _
      calc ‖(x - e (f p)) + (e (f p) - e p)‖
        ≤ ‖x - e (f p)‖ + ‖e (f p) - e p‖ := h_tri
      _ ≤ Real.sqrt 2 * δ + Real.sqrt 2 * (δ / 2) := by gcongr
      _ = Real.sqrt 2 * (3 * δ / 2) := by ring
    have h_ep_in : e p ∈ e '' Tz := Set.mem_image_of_mem e hp
    have h_edist : edist x (e p) ≤ ENNReal.ofReal (Real.sqrt 2 * (3 * δ / 2)) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal h_dist3
    have h_inf : Metric.infEDist x (e '' Tz) ≤ edist x (e p) :=
      Metric.infEDist_le_edist_of_mem h_ep_in
    exact h_inf.trans h_edist

  exact ⟨𝒯z, h1, h_product, h2, h_encard_lower, h_thicken⟩


/-! ### Helper: canonical parameter cube is a dyadic cube -/

/-- The canonical parameter cube of an appendix dyadic tube is a dyadic cube. -/
lemma canonicalCube_is_dyadic (δ : ℝ) (T : Set (EuclideanSpace ℝ (Fin 2)))
    (hT : T ∈ appendixDyadicTubes δ) :
    ∃ (k : Fin 2 → ℤ), productLikeAppendixDyadicTubeCanonicalParameterCube δ T = dyadicCube δ k := by
  have h1 : productLikeAppendixDyadicTubeCanonicalParameterCube δ T ∈
      dyadicCubes (d := 2) δ := by
    have h2 : productLikeAppendixDyadicTubeCanonicalParameterCube δ T =
        Classical.choose hT := by
      unfold productLikeAppendixDyadicTubeCanonicalParameterCube
      rw [dif_pos hT] <;> rfl
    rw [h2]
    have h3 : (Classical.choose hT) ∈ dyadicCubesMeeting (d := 2) δ appendixParameterStrip :=
      (Classical.choose_spec hT).1
    exact h3.1
  rcases h1 with ⟨k, hk⟩
  exact ⟨k, hk⟩

/-! ### Helper: encard of union comparable to covering number -/

/-- The encard of a union of tube families is comparable to the metric
covering number of the union of their parameter sets. -/
lemma tubeUnion_encard_comparable {δ : ℝ} (hδ : 0 < δ)
    {ι : Type*} {S : Set ι}
    {𝒯 : ι → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (h : ∀ i ∈ S, 𝒯 i ⊆ appendixDyadicTubes δ) :
    ENat.toENNReal (⋃ i ∈ S, 𝒯 i).encard ≥
      (Metric.externalCoveringNumber δ.toNNReal
         (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) : ENNReal) / 1000 := by
  let 𝒯_union : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ i ∈ S, 𝒯 i
  let P_union : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)

  have hT_appendix : ∀ T ∈ 𝒯_union, T ∈ appendixDyadicTubes δ := by
    intro T hT
    have h_exists : ∃ (i : ι), i ∈ S ∧ T ∈ 𝒯 i := by
      simpa [𝒯_union] using hT
    rcases h_exists with ⟨i, hi, hTi⟩
    exact h i hi hTi

  classical

  let center (T : Set (EuclideanSpace ℝ (Fin 2))) : EuclideanSpace ℝ (Fin 2) :=
    if hT : T ∈ 𝒯_union then
      let k : Fin 2 → ℤ := Classical.choose (canonicalCube_is_dyadic δ T (hT_appendix T hT))
      WithLp.toLp 2 (fun i : Fin 2 => δ * ((k i : ℝ) + 1 / 2))
    else 0

  have h_cube_subset_ball : ∀ T ∈ 𝒯_union,
      productLikeAppendixDyadicTubeCanonicalParameterCube δ T ⊆
      Metric.closedBall (center T) δ := by
    intro T hT
    let k : Fin 2 → ℤ := Classical.choose (canonicalCube_is_dyadic δ T (hT_appendix T hT))
    have hk : productLikeAppendixDyadicTubeCanonicalParameterCube δ T = dyadicCube δ k :=
      Classical.choose_spec (canonicalCube_is_dyadic δ T (hT_appendix T hT))
    let cT : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun i : Fin 2 => δ * ((k i : ℝ) + 1 / 2))
    have h_center_eq : center T = cT := by
      unfold center
      rw [dif_pos hT] <;> rfl
    have h_ball : dyadicCube δ k ⊆ Metric.closedBall cT δ := by
      intro x hx
      have h3 : ∀ i : Fin 2, |x i - δ * ((k i : ℝ) + 1 / 2)| ≤ δ / 2 := by
        intro i
        have h4 : δ * (k i : ℝ) ≤ x i := (hx i).1
        have h5 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
        have h6 : -δ / 2 ≤ x i - δ * ((k i : ℝ) + 1 / 2) := by linarith
        have h7 : x i - δ * ((k i : ℝ) + 1 / 2) < δ / 2 := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h8 : ‖x - cT‖ ^ 2 ≤ ∑ i : Fin 2, (δ / 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        have h9 : ∀ i : Fin 2, (x i - δ * ((k i : ℝ) + 1 / 2)) ^ 2 ≤ (δ / 2) ^ 2 := by
          intro i
          have h10 : |x i - δ * ((k i : ℝ) + 1 / 2)| ≤ δ / 2 := h3 i
          have h11 : (x i - δ * ((k i : ℝ) + 1 / 2)) ^ 2 =
              |x i - δ * ((k i : ℝ) + 1 / 2)| ^ 2 := by rw [sq_abs]
          rw [h11]; gcongr <;> linarith
        apply Finset.sum_le_sum
        intro i _
        exact h9 i
      have h12 : (∑ i : Fin 2, (δ / 2) ^ 2) = 2 * (δ / 2) ^ 2 := by
        simp [Finset.sum_const] <;> ring
      rw [h12] at h8
      have h13 : ‖x - cT‖ ≤ δ := by
        have h14 : 0 ≤ ‖x - cT‖ := by positivity
        nlinarith
      exact h13
    have h_goal : productLikeAppendixDyadicTubeCanonicalParameterCube δ T ⊆
        Metric.closedBall (center T) δ := by
      rw [h_center_eq]
      rw [hk]
      exact h_ball
    exact h_goal

  let Centers : Set (EuclideanSpace ℝ (Fin 2)) := center '' 𝒯_union

  have h_cover : P_union ⊆ ⋃ c ∈ Centers, Metric.closedBall c δ := by
    intro x hx
    have h15 : ∃ (i : ι), i ∈ S ∧ x ∈ productLikeAppendixDyadicTubeParameterSet δ (𝒯 i) := by
      simpa [P_union, Set.mem_biUnion] using hx
    rcases h15 with ⟨i, hi, hxi⟩
    have h16 : ∃ (C : Set (EuclideanSpace ℝ (Fin 2))),
        C ∈ productLikeAppendixDyadicTubeCanonicalParameterCube δ '' 𝒯 i ∧ x ∈ C := by
      simpa [productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion] using hxi
    rcases h16 with ⟨C, ⟨T, hT, rfl⟩, hxC⟩
    have hT_union : T ∈ 𝒯_union := by
      have h : ∃ (i : ι), i ∈ S ∧ T ∈ 𝒯 i := ⟨i, hi, hT⟩
      simpa [𝒯_union] using h
    let cT := center T
    have hcT_in : cT ∈ Centers := ⟨T, hT_union, rfl⟩
    have h17 : x ∈ Metric.closedBall cT δ := h_cube_subset_ball T hT_union hxC
    have h18 : x ∈ ⋃ c ∈ Centers, Metric.closedBall c δ := by
      have h : ∃ (c : EuclideanSpace ℝ (Fin 2)), c ∈ Centers ∧ x ∈ Metric.closedBall c δ := ⟨cT, hcT_in, h17⟩
      simpa using h
    exact h18

  have hIsCover : Metric.IsCover δ.toNNReal P_union Centers := by
    intro x hx
    have h20 : x ∈ ⋃ c ∈ Centers, Metric.closedBall c δ := h_cover hx
    have h_exists2 : ∃ (c : EuclideanSpace ℝ (Fin 2)), c ∈ Centers ∧ x ∈ Metric.closedBall c δ := by
      simpa using h20
    rcases h_exists2 with ⟨c, hc, hball⟩
    have h22 : dist x c ≤ δ := by
      simpa [Metric.mem_closedBall] using hball
    have h21 : edist x c ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h23 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
      rw [h23]
      exact ENNReal.ofReal_le_ofReal h22
    exact ⟨c, hc, h21⟩

  have h_main1 : Metric.externalCoveringNumber δ.toNNReal P_union ≤ Centers.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hIsCover

  have h_main2 : Centers.encard ≤ 𝒯_union.encard := Set.encard_image_le center 𝒯_union

  have h_final : (Metric.externalCoveringNumber δ.toNNReal P_union : ENNReal) ≤
      ENat.toENNReal 𝒯_union.encard := by
    exact_mod_cast h_main1.trans h_main2

  have h_div : (Metric.externalCoveringNumber δ.toNNReal P_union : ENNReal) / 1000 ≤
      ENat.toENNReal 𝒯_union.encard := by
    have h_le : (Metric.externalCoveringNumber δ.toNNReal P_union : ENNReal) / 1000 ≤
        (Metric.externalCoveringNumber δ.toNNReal P_union : ENNReal) := by
      let X := (Metric.externalCoveringNumber δ.toNNReal P_union : ENNReal)
      have h2 : (1000 : ENNReal)⁻¹ ≤ 1 := by norm_num
      have h3 : X * (1000 : ENNReal)⁻¹ ≤ X * 1 := mul_le_mul_left' h2 X
      have h4 : X * 1 = X := by simp
      have h5 : X / 1000 = X * (1000 : ENNReal)⁻¹ := by
        simp [div_eq_mul_inv]
      rw [h5]
      rw [h4] at h3
      exact h3
    exact h_le.trans h_final

  exact h_div

/-! ### Translation and scaling lemmas for IsDeltaSSet -/

/-- Translation preserves the S-set property in 1D. -/
lemma IsDeltaSSet.translate1 {δ s C : ℝ} {A : Set ℝ} {b : ℝ}
    (hP : IsDeltaSSet δ s C A) :
    IsDeltaSSet δ s C ((fun x : ℝ => x + b) '' A) := by
  let e : ℝ ≃ᵢ ℝ :=
    { toFun := fun x => x + b
      invFun := fun y => y - b
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [dist_eq_norm] <;> ring }
  set B : Set ℝ := e '' A with hB
  have hcov_eq : Metric.externalCoveringNumber δ.toNNReal B =
      Metric.externalCoveringNumber δ.toNNReal A :=
    externalCoveringNumber_image_isometryEquiv e
  have h_main : ∀ (x : ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
    hP.2.2.2.2
  refine ⟨hP.1.image e, hP.2.1, hP.2.2.1, hP.2.2.2.1, ?_⟩
  intro y r hr
  set x : ℝ := y - b with hx_def
  have h_ex : e x = y := by simp [e, hx_def] <;> ring
  have h_ball : e '' Metric.closedBall x r = Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h4 : dist (e w) (e x) ≤ r := by
        have h5 : dist (e w) (e x) = dist w x := e.dist_eq w x
        rw [h5]; exact hw
      rw [h_ex] at *; exact h4
    · intro hz
      refine ⟨e.symm z, ?_, ?_⟩
      · have h7 : dist (e.symm z) x ≤ r := by
          have h8 : dist (e.symm z) x = dist z (e x) := by
            have h9 : dist (e (e.symm z)) (e x) = dist (e.symm z) x := e.dist_eq (e.symm z) x
            have h10 : e (e.symm z) = z := e.apply_symm_apply z
            rw [h10] at h9
            exact h9.symm
          rw [h8, h_ex]; exact hz
        exact h7
      · exact e.apply_symm_apply z
  have h_inj : Function.Injective e := e.injective
  have h_img_inter : e '' (A ∩ Metric.closedBall x r) = B ∩ Metric.closedBall y r := by
    rw [Set.image_inter h_inj, h_ball, hB]
  have h5 : (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := by
    rw [←h_img_inter]
    exact_mod_cast externalCoveringNumber_image_isometryEquiv e
  have hB' : (fun x : ℝ => x + b) '' A = B := hB.symm
  rw [hB']
  rw [h5, hcov_eq]
  exact h_main x r hr

/-- Translation preserves the S-set property in 2D. -/
lemma IsDeltaSSet.translate2 {δ s C : ℝ} {A : Set (ℝ × ℝ)} {b : ℝ × ℝ}
    (hP : IsDeltaSSet δ s C A) :
    IsDeltaSSet δ s C ((fun p : ℝ × ℝ => (p.1 + b.1, p.2 + b.2)) '' A) := by
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 + b.1, p.2 + b.2)
  let g : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 - b.1, p.2 - b.2)
  have h_iso : Isometry f := by
    intro p q
    have h_dist : dist (f p) (f q) = dist p q := by
      simp [f, Prod.dist_eq, dist_eq_norm] <;> rfl
    have h_edist : edist (f p) (f q) = edist p q := by
      rw [edist_dist, edist_dist, h_dist]
    exact h_edist
  let e : (ℝ × ℝ) ≃ᵢ (ℝ × ℝ) :=
    { toFun := f
      invFun := g
      left_inv := by intro p; ext <;> simp [f, g] <;> ring
      right_inv := by intro p; ext <;> simp [f, g] <;> ring
      isometry_toFun := h_iso }
  set B : Set (ℝ × ℝ) := e '' A with hB
  have hcov_eq : Metric.externalCoveringNumber δ.toNNReal B =
      Metric.externalCoveringNumber δ.toNNReal A :=
    externalCoveringNumber_image_isometryEquiv e
  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
    hP.2.2.2.2
  refine ⟨hP.1.image e, hP.2.1, hP.2.2.1, hP.2.2.2.1, ?_⟩
  intro y r hr
  set x : ℝ × ℝ := e.symm y with hx_def
  have h_ex : e x = y := e.apply_symm_apply y
  have h_ball : e '' Metric.closedBall x r = Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h4 : dist (e w) (e x) ≤ r := by
        have h5 : dist (e w) (e x) = dist w x := e.dist_eq w x
        rw [h5]; exact hw
      rw [h_ex] at *; exact h4
    · intro hz
      refine ⟨e.symm z, ?_, ?_⟩
      · have h7 : dist (e.symm z) x ≤ r := by
          have h8 : dist (e.symm z) x = dist z (e x) := by
            have h9 : dist (e (e.symm z)) (e x) = dist (e.symm z) x := e.dist_eq (e.symm z) x
            have h10 : e (e.symm z) = z := e.apply_symm_apply z
            rw [h10] at h9
            exact h9.symm
          rw [h8, h_ex]; exact hz
        exact h7
      · exact e.apply_symm_apply z
  have h_inj : Function.Injective e := e.injective
  have h_img_inter : e '' (A ∩ Metric.closedBall x r) = B ∩ Metric.closedBall y r := by
    rw [Set.image_inter h_inj, h_ball, hB]
  have h5 : (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal) =
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := by
    rw [←h_img_inter]
    exact_mod_cast externalCoveringNumber_image_isometryEquiv e
  have hB' : (fun p : ℝ × ℝ => (p.1 + b.1, p.2 + b.2)) '' A = B := hB.symm
  rw [hB']
  rw [h5, hcov_eq]
  exact h_main x r hr

/-- Scaling by λ in 1D: (δ,s,C)-set → (λδ,s,C/λ^s)-set. -/
lemma IsDeltaSSet.scale1 {δ s C : ℝ} {A : Set ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hP : IsDeltaSSet δ s C A) :
    IsDeltaSSet (lam * δ) s (C / lam ^ s) ((fun x : ℝ => lam * x) '' A) := by
  have hδ : 0 < δ := hP.2.1
  have hC : 0 < C := hP.2.2.1
  have hs : 0 ≤ s := hP.2.2.2.1
  let f : ℝ → ℝ := fun x => lam * x
  let g : ℝ → ℝ := fun y => y / lam
  let lam_nn : NNReal := ⟨lam, show 0 ≤ lam from by linarith⟩
  let inv_lam_nn : NNReal := lam_nn⁻¹
  set B : Set ℝ := f '' A with hB
  have hf_inj : Function.Injective f := by
    intro x y h; exact mul_left_cancel₀ hlam.ne' h
  have hf_lip : LipschitzWith lam_nn f :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h : dist (f x) (f y) = lam * dist x y := real_homothety_dist lam hlam x y
      rw [h] <;> exact le_refl _
  have hg_lip : LipschitzWith inv_lam_nn g :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h_coe : (↑inv_lam_nn : ℝ) = 1 / lam := by
        have h_lam_nn_coe : (↑lam_nn : ℝ) = lam := by simp [lam_nn] <;> rfl
        have h : (↑inv_lam_nn : ℝ) = (↑lam_nn : ℝ)⁻¹ := by simp [inv_lam_nn, NNReal.coe_inv]
        rw [h, h_lam_nn_coe] <;> field_simp [hlam.ne']
      have h : dist (g x) (g y) = (1 / lam) * dist x y := by
        calc dist (g x) (g y)
          = |x / lam - y / lam| := by simp [g, dist_eq_norm]
        _ = |(x - y) / lam| := by ring_nf
        _ = |x - y| / |lam| := by rw [abs_div]
        _ = |x - y| / lam := by rw [abs_of_pos hlam]
        _ = (1 / lam) * dist x y := by simp [dist_eq_norm] <;> ring
      rw [h, h_coe] <;> exact le_refl _
  have h1 : lam_nn * δ.toNNReal = (lam * δ).toNNReal :=
    nnreal_mul_toNNReal_general lam_nn δ hδ
  have h2 : inv_lam_nn * (lam * δ).toNNReal = δ.toNNReal :=
    nnreal_inv_mul_toNNReal_general lam_nn hlam δ hδ
  have hgf : ∀ x, g (f x) = x := by
    intro x; simp [f, g]; field_simp [hlam.ne'] <;> ring
  have hgA : g '' B = A := by
    rw [hB]; ext z; simp only [Set.mem_image]; constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; rw [hgf x]; exact hx
    · intro hz; refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩; exact hgf z
  have hcov_eq : Metric.externalCoveringNumber (lam * δ).toNNReal B =
      Metric.externalCoveringNumber δ.toNNReal A := by
    have h_le : Metric.externalCoveringNumber (lam * δ).toNNReal B ≤
        Metric.externalCoveringNumber δ.toNNReal A := by
      have h := externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δ.toNNReal) (A := A)
      rw [h1] at h; exact h
    have h_ge : Metric.externalCoveringNumber δ.toNNReal A ≤
        Metric.externalCoveringNumber (lam * δ).toNNReal B := by
      have h := externalCoveringNumber_image_lipschitz (hf := hg_lip) (ε := (lam * δ).toNNReal) (A := B)
      rw [h2, hgA] at h; exact h
    exact le_antisymm h_le h_ge
  have h_main : ∀ (x : ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := hP.2.2.2.2
  have hlamδ_pos : 0 < lam * δ := mul_pos hlam hδ
  have hC_div_pos : 0 < C / lam ^ s := by positivity
  refine ⟨hP.1.image f, hlamδ_pos, hC_div_pos, hs, ?_⟩
  intro y r hr
  set x : ℝ := y / lam with hx_def
  set r' : ℝ := r / lam with hr'_def
  have hr'_ge_δ : δ ≤ r' := by
    rw [hr'_def]
    have h : r ≥ lam * δ := hr
    have h' : r / lam ≥ δ := by
      calc r / lam ≥ (lam * δ) / lam := by gcongr
        _ = δ := by field_simp [hlam.ne'] <;> ring
    exact h'
  have hfx : f x = y := by simp [f, hx_def]; field_simp [hlam.ne'] <;> ring
  have h3 : f '' Metric.closedBall x r' = Metric.closedBall y r := by
    have h4 := image_closedBall_homothety lam hlam x r'
    have h5 : lam * x = y := by simp [f, hx_def]; field_simp [hlam.ne'] <;> ring
    have h6 : lam * r' = r := by simp [r']; field_simp [hlam.ne'] <;> ring
    rw [h5, h6] at h4; exact h4
  have h4 : f '' (A ∩ Metric.closedBall x r') = B ∩ Metric.closedBall y r := by
    rw [Set.image_inter hf_inj, h3, hB]
  have h_cov_img : Metric.externalCoveringNumber (lam_nn * δ.toNNReal)
      (f '' (A ∩ Metric.closedBall x r')) ≤
      Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') :=
    externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δ.toNNReal) (A := A ∩ Metric.closedBall x r')
  have h5 : (Metric.externalCoveringNumber (lam * δ).toNNReal (B ∩ Metric.closedBall y r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) := by
    rw [h1] at h_cov_img
    rw [h4] at h_cov_img
    exact_mod_cast h_cov_img
  have h6 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h_main x r' hr'_ge_δ
  have h_real_eq : C * (r' ^ s) = (C / lam ^ s) * (r ^ s) := by
    have h9 : r' = r / lam := by simp [r']
    rw [h9]
    have h10 : (r / lam) ^ s = r ^ s / lam ^ s := by
      have h_div : r / lam = r * lam⁻¹ := by ring
      rw [h_div, Real.mul_rpow (by linarith) (by positivity)]
      have h11 : (lam⁻¹) ^ s = (lam ^ s)⁻¹ := by
        have h12 : 0 ≤ lam := by linarith
        have h13 : lam⁻¹ = lam ^ (-1 : ℝ) := by
          have h14 : lam ^ (-1 : ℝ) = lam⁻¹ := by
            simp [Real.rpow_neg (show 0 ≤ lam from by linarith)] <;> ring
          exact h14.symm
        rw [h13]
        have h15 : (lam ^ (-1 : ℝ)) ^ s = lam ^ ((-1 : ℝ) * s) := by
          rw [Real.rpow_mul (show 0 ≤ lam from by linarith)] <;> ring
        rw [h15]
        have h16 : (-1 : ℝ) * s = -s := by ring
        rw [h16, Real.rpow_neg (show 0 ≤ lam from by linarith)]
      rw [h11] <;> ring
    rw [h10] <;> field_simp [hlam.ne'] <;> ring
  have h_ennreal_eq : ENNReal.ofReal C * (ENNReal.ofReal r') ^ s =
      ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s := by
    have hC_nonneg : 0 ≤ C := by linarith
    have hr'_nonneg : 0 ≤ r' := by linarith
    have hr_nonneg : 0 ≤ r := by linarith
    have h_mul1 : ENNReal.ofReal (C * (r' ^ s)) =
        ENNReal.ofReal C * ENNReal.ofReal (r' ^ s) := by exact ENNReal.ofReal_mul hC_nonneg
    have h1 : ENNReal.ofReal C * (ENNReal.ofReal r') ^ s =
        ENNReal.ofReal (C * (r' ^ s)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr'_nonneg hs]; exact h_mul1.symm
    have hdiv_nonneg : 0 ≤ C / lam ^ s := by positivity
    have h_mul2 : ENNReal.ofReal ((C / lam ^ s) * (r ^ s)) =
        ENNReal.ofReal (C / lam ^ s) * ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_mul hdiv_nonneg]
    have h2 : ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s =
        ENNReal.ofReal ((C / lam ^ s) * (r ^ s)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs]; exact h_mul2.symm
    rw [h1, h2, h_real_eq]
  calc
    (Metric.externalCoveringNumber (lam * δ).toNNReal (B ∩ Metric.closedBall y r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h6
    _ = ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (lam * δ).toNNReal B : ENNReal) := by
      rw [h_ennreal_eq, hcov_eq]

/-- Scaling by λ in 2D: (δ,s,C)-set → (λδ,s,C/λ^s)-set. -/
lemma IsDeltaSSet.scale2 {δ s C : ℝ} {A : Set (ℝ × ℝ)} {lam : ℝ} (hlam : 0 < lam)
    (hP : IsDeltaSSet δ s C A) :
    IsDeltaSSet (lam * δ) s (C / lam ^ s) ((fun p : ℝ × ℝ => (lam * p.1, lam * p.2)) '' A) := by
  have hδ : 0 < δ := hP.2.1
  have hC : 0 < C := hP.2.2.1
  have hs : 0 ≤ s := hP.2.2.2.1
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (lam * p.1, lam * p.2)
  let g : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 / lam, p.2 / lam)
  let lam_nn : NNReal := ⟨lam, show 0 ≤ lam from by linarith⟩
  let inv_lam_nn : NNReal := lam_nn⁻¹
  set B : Set (ℝ × ℝ) := f '' A with hB
  have hf_inj : Function.Injective f := by
    intro p q h
    have h1 : lam * p.1 = lam * q.1 := by exact congr_arg Prod.fst h
    have h2 : lam * p.2 = lam * q.2 := by exact congr_arg Prod.snd h
    exact Prod.ext (mul_left_cancel₀ hlam.ne' h1) (mul_left_cancel₀ hlam.ne' h2)
  have hf_surj : Function.Surjective f := by
    intro y; refine ⟨(y.1 / lam, y.2 / lam), ?_⟩; simp [f]; field_simp [hlam.ne'] <;> ring
  have hf_lip : LipschitzWith lam_nn f :=
    LipschitzWith.of_dist_le_mul fun p q => by
      have h : dist (f p) (f q) = lam * dist p q := prod_homothety_dist lam hlam p q
      rw [h] <;> exact le_refl _
  have hg_lip : LipschitzWith inv_lam_nn g :=
    LipschitzWith.of_dist_le_mul fun p q => by
      have h_coe : (↑inv_lam_nn : ℝ) = 1 / lam := by
        have h_lam_nn_coe : (↑lam_nn : ℝ) = lam := by simp [lam_nn] <;> rfl
        have h : (↑inv_lam_nn : ℝ) = (↑lam_nn : ℝ)⁻¹ := by simp [inv_lam_nn, NNReal.coe_inv]
        rw [h, h_lam_nn_coe] <;> field_simp [hlam.ne']
      have h_step1 : dist (g p) (g q) =
          max (|p.1 / lam - q.1 / lam|) (|p.2 / lam - q.2 / lam|) := by
        simp [g, Prod.dist_eq] <;> rfl
      have h_abs1 : |p.1 / lam - q.1 / lam| = |p.1 - q.1| / lam := by
        have h_eq : p.1 / lam - q.1 / lam = (p.1 - q.1) / lam := by ring
        rw [h_eq, abs_div, abs_of_pos hlam]
      have h_abs2 : |p.2 / lam - q.2 / lam| = |p.2 - q.2| / lam := by
        have h_eq : p.2 / lam - q.2 / lam = (p.2 - q.2) / lam := by ring
        rw [h_eq, abs_div, abs_of_pos hlam]
      have h_step2 : max (|p.1 / lam - q.1 / lam|) (|p.2 / lam - q.2 / lam|) =
          max (|p.1 - q.1| / lam) (|p.2 - q.2| / lam) := by
        rw [h_abs1, h_abs2]
      have h_max_div : ∀ (a b : ℝ), max (a / lam) (b / lam) = (1 / lam) * max a b := by
        intro a b
        cases' le_total a b with h h
        · have h4 : a / lam ≤ b / lam := by gcongr
          rw [max_eq_right h, max_eq_right h4] <;> ring
        · have h4 : b / lam ≤ a / lam := by gcongr
          rw [max_eq_left h4, max_eq_left h] <;> ring
      have h_dist : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by
        simp [Prod.dist_eq, dist_eq_norm] <;> rfl
      have h_step3 : max (|p.1 - q.1| / lam) (|p.2 - q.2| / lam) =
          (1 / lam) * dist p q := by
        rw [h_dist]; exact h_max_div (|p.1 - q.1|) (|p.2 - q.2|)
      have h : dist (g p) (g q) = (1 / lam) * dist p q := by
        rw [h_step1, h_step2, h_step3]
      rw [h, h_coe] <;> exact le_refl _
  have h1 : lam_nn * δ.toNNReal = (lam * δ).toNNReal :=
    nnreal_mul_toNNReal_general lam_nn δ hδ
  have h2 : inv_lam_nn * (lam * δ).toNNReal = δ.toNNReal :=
    nnreal_inv_mul_toNNReal_general lam_nn hlam δ hδ
  have hgf : ∀ p, g (f p) = p := by
    intro p; simp [f, g]; field_simp [hlam.ne'] <;> ring
  have hgA : g '' B = A := by
    rw [hB]; ext z; simp only [Set.mem_image]; constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩; rw [hgf x]; exact hx
    · intro hz; refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩; exact hgf z
  have hcov_eq : Metric.externalCoveringNumber (lam * δ).toNNReal B =
      Metric.externalCoveringNumber δ.toNNReal A := by
    have h_le := externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δ.toNNReal) (A := A)
    have h_ge := externalCoveringNumber_image_lipschitz (hf := hg_lip) (ε := (lam * δ).toNNReal) (A := B)
    rw [h1] at h_le; rw [h2, hgA] at h_ge
    exact le_antisymm h_le h_ge
  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := hP.2.2.2.2
  have hlamδ_pos : 0 < lam * δ := mul_pos hlam hδ
  have hC_div_pos : 0 < C / lam ^ s := by positivity
  refine ⟨hP.1.image f, hlamδ_pos, hC_div_pos, hs, ?_⟩
  intro y r hr
  set x : ℝ × ℝ := g y with hx_def
  set r' : ℝ := r / lam with hr'_def
  have hr'_ge_δ : δ ≤ r' := by
    rw [hr'_def]
    have h : r ≥ lam * δ := hr
    have h' : r / lam ≥ δ := by
      calc r / lam ≥ (lam * δ) / lam := by gcongr
        _ = δ := by field_simp [hlam.ne'] <;> ring
    exact h'
  have hfx : f x = y := by simp [f, hx_def, g]; field_simp [hlam.ne'] <;> ring
  have h3 : f '' Metric.closedBall x r' = Metric.closedBall y r := by
    have h4 := image_closedBall_homothety_general f lam hlam
      (prod_homothety_dist lam hlam) hf_surj x r'
    have h5 : f x = y := hfx
    have h6 : lam * r' = r := by simp [r']; field_simp [hlam.ne'] <;> ring
    rw [h5, h6] at h4; exact h4
  have h4 : f '' (A ∩ Metric.closedBall x r') = B ∩ Metric.closedBall y r := by
    rw [Set.image_inter hf_inj, h3, hB]
  have h_cov_img : Metric.externalCoveringNumber (lam_nn * δ.toNNReal)
      (f '' (A ∩ Metric.closedBall x r')) ≤
      Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') :=
    externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δ.toNNReal) (A := A ∩ Metric.closedBall x r')
  have h5 : (Metric.externalCoveringNumber (lam * δ).toNNReal (B ∩ Metric.closedBall y r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) := by
    rw [h1] at h_cov_img
    rw [h4] at h_cov_img
    exact_mod_cast h_cov_img
  have h6 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h_main x r' hr'_ge_δ
  have h_real_eq : C * (r' ^ s) = (C / lam ^ s) * (r ^ s) := by
    have h9 : r' = r / lam := by simp [r']
    rw [h9]
    have h10 : (r / lam) ^ s = r ^ s / lam ^ s := by
      have h_div : r / lam = r * lam⁻¹ := by ring
      rw [h_div, Real.mul_rpow (by linarith) (by positivity)]
      have h11 : (lam⁻¹) ^ s = (lam ^ s)⁻¹ := by
        have h12 : 0 ≤ lam := by linarith
        have h13 : lam⁻¹ = lam ^ (-1 : ℝ) := by
          have h14 : lam ^ (-1 : ℝ) = lam⁻¹ := by
            simp [Real.rpow_neg (show 0 ≤ lam from by linarith)] <;> ring
          exact h14.symm
        rw [h13]
        have h15 : (lam ^ (-1 : ℝ)) ^ s = lam ^ ((-1 : ℝ) * s) := by
          rw [Real.rpow_mul (show 0 ≤ lam from by linarith)] <;> ring
        rw [h15]
        have h16 : (-1 : ℝ) * s = -s := by ring
        rw [h16, Real.rpow_neg (show 0 ≤ lam from by linarith)]
      rw [h11] <;> ring
    rw [h10] <;> field_simp [hlam.ne'] <;> ring
  have h_ennreal_eq : ENNReal.ofReal C * (ENNReal.ofReal r') ^ s =
      ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s := by
    have hC_nonneg : 0 ≤ C := by linarith
    have hr'_nonneg : 0 ≤ r' := by linarith
    have hr_nonneg : 0 ≤ r := by linarith
    have h_mul1 : ENNReal.ofReal (C * (r' ^ s)) =
        ENNReal.ofReal C * ENNReal.ofReal (r' ^ s) := by exact ENNReal.ofReal_mul hC_nonneg
    have h1 : ENNReal.ofReal C * (ENNReal.ofReal r') ^ s =
        ENNReal.ofReal (C * (r' ^ s)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr'_nonneg hs]; exact h_mul1.symm
    have hdiv_nonneg : 0 ≤ C / lam ^ s := by positivity
    have h_mul2 : ENNReal.ofReal ((C / lam ^ s) * (r ^ s)) =
        ENNReal.ofReal (C / lam ^ s) * ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_mul hdiv_nonneg]
    have h2 : ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s =
        ENNReal.ofReal ((C / lam ^ s) * (r ^ s)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs]; exact h_mul2.symm
    rw [h1, h2, h_real_eq]
  calc
    (Metric.externalCoveringNumber (lam * δ).toNNReal (B ∩ Metric.closedBall y r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r') : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h6
    _ = ENNReal.ofReal (C / lam ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (lam * δ).toNNReal B : ENNReal) := by
      rw [h_ennreal_eq, hcov_eq]

/-! ### Interval covering helper for scale-up -/
