/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Thickness.Homothety
public import Kakeya.Thickness.Lemmas
public import Kakeya.Density
public import Kakeya.Homothety
public import Kakeya.Frostman

/-!
# Discretization of convex bodies by rectangular prisms

We state a polynomial-size discretization theorem first for bounded rectangular prisms.
The corresponding result for convex bodies follows by applying the prism theorem to the
outer prism of each convex body.
-/

@[expose] public section

open MeasureTheory Module

namespace Kakeya

universe v

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The constant in `FiniteDimensional.discretizeBallAt` -/
noncomputable abbrev FiniteDimensional.discretizeBallAt.C (dim : ℕ) : NNReal :=
  (4 * NNReal.sqrt dim + 5) ^ dim

omit [MeasurableSpace E] [BorelSpace E] in
/-- Discretize an $R$-ball in a Euclidean space at scale r -/
theorem FiniteDimensional.discretizeBallAt {r R : NNReal} (hr : 0 < r) (hR : r ≤ R) :
    ∃ D : Finset E,
      (D.card : NNReal) ≤ FiniteDimensional.discretizeBallAt.C (Module.finrank ℝ E) *
        (R / r) ^ Module.finrank ℝ E ∧
      (∀ c ∈ D, c ∈ Metric.closedBall (0 : E) R) ∧
      (∀ x ∈ Metric.closedBall (0 : E) R, ∃ y ∈ D, dist x y ≤ r) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hn_real_pos : (0 : ℝ) < n := by norm_cast; exact finrank_pos
  set b := stdOrthonormalBasis ℝ E
  set hStep : ℝ := r / Real.sqrt n
  have hStep_pos : 0 < hStep := by positivity
  set K : ℤ := Int.ceil (R / hStep)
  have hK_nonneg : 0 ≤ K := by
    apply Int.ceil_nonneg
    positivity
  set L : Finset (Fin n → ℤ) :=
    Fintype.piFinset (fun _ : Fin n ↦ Finset.Icc (-K) K)
  set D₀ : Finset E := L.image (fun k : Fin n → ℤ ↦
    b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ))))
  set D := {y ∈ D₀ | y ∈ Metric.closedBall (0 : E) R}
  use D
  constructor
  · have hcard : D.card ≤ (2 * K.toNat + 1) ^ n := by
      calc
        D.card ≤ D₀.card := by simpa only [D] using Finset.card_filter_le D₀ _
        _ ≤ L.card := Finset.card_image_le
        _ = ∏ _i : Fin n, (Finset.Icc (-K) K).card := by
          simp only [L, Fintype.card_piFinset]
        _ = (2 * K.toNat + 1) ^ n := by
          simp only [Int.card_Icc]
          have hIcc : (K + 1 - -K).toNat = 2 * K.toNat + 1 := by omega
          rw [hIcc]
          simp
    calc
      (D.card : NNReal) ≤ (((2 * K.toNat + 1) ^ n : ℕ) : NNReal) := by
        exact_mod_cast hcard
      _ = (((2 * K.toNat + 1 : ℕ) : NNReal) ^ n) := by norm_cast
      _ ≤ ((4 * NNReal.sqrt n + 5) * (R / r)) ^ n := by
        gcongr
        have hK_lt : (K : ℝ) < (R : ℝ) / hStep + 1 := Int.ceil_lt_add_one _
        have hK_toNat : (K.toNat : ℝ) = K := by
          exact_mod_cast Int.toNat_of_nonneg hK_nonneg
        have hratio : (1 : ℝ) ≤ (R : ℝ) / r := by
          rw [le_div_iff₀ (by exact_mod_cast hr)]
          simpa using (show (r : ℝ) ≤ R by exact_mod_cast hR)
        rw [← NNReal.coe_le_coe]
        push_cast
        have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have hrewrite : (R : ℝ) / hStep = ((R : ℝ) / r) * Real.sqrt n := by
          change (R : ℝ) / ((r : ℝ) / Real.sqrt n) = _
          field_simp
        rw [hrewrite] at hK_lt
        rw [hK_toNat]
        nlinarith
      _ = FiniteDimensional.discretizeBallAt.C n * (R / r) ^ n := by rw [mul_pow]
  constructor
  · intro c hc
    change c ∈ {y ∈ D₀ | y ∈ Metric.closedBall (0 : E) R} at hc
    exact (Finset.mem_filter.mp hc).2
  · intro c hc
    have hc_norm : ‖c‖ ≤ R := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hc
    set x := (b.repr c).ofLp with hx_def
    have hx_norm : ‖x‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      rw [hx_def]
      calc
        ‖(b.repr c).ofLp i‖ ≤ ‖b.repr c‖ := PiLp.norm_apply_le _ _
        _ = ‖c‖ := b.repr.norm_map c
        _ ≤ R := hc_norm
    set k : Fin n → ℤ := fun i ↦
      if x i ≥ 0 then Int.floor (x i / hStep) else -Int.floor (-x i / hStep) with hk_def
    have hk_abs : ∀ i, |k i| ≤ K := by
      intro i
      have hxi_abs : |x i| ≤ (R : ℝ) := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hx_norm
      change |if 0 ≤ x i then Int.floor (x i / hStep)
        else -Int.floor (-x i / hStep)| ≤ K
      by_cases hxi : 0 ≤ x i
      · rw [if_pos hxi, abs_of_nonneg]
        · change Int.floor (x i / hStep) ≤ Int.ceil ((R : ℝ) / hStep)
          refine (Int.floor_mono ?_).trans (Int.floor_le_ceil _)
          exact div_le_div_of_nonneg_right ((le_abs_self _).trans hxi_abs) hStep_pos.le
        · exact Int.floor_nonneg.mpr (div_nonneg hxi hStep_pos.le)
      · rw [if_neg hxi, abs_neg, abs_of_nonneg]
        · change Int.floor (-x i / hStep) ≤ Int.ceil ((R : ℝ) / hStep)
          refine (Int.floor_mono ?_).trans (Int.floor_le_ceil _)
          apply div_le_div_of_nonneg_right _ hStep_pos.le
          linarith [(abs_le.mp hxi_abs).1]
        · exact Int.floor_nonneg.mpr
            (div_nonneg (neg_nonneg.mpr (le_of_not_ge hxi)) hStep_pos.le)
    have hk_in_L : k ∈ L := by
      change k ∈ Fintype.piFinset (fun _ : Fin n ↦ Finset.Icc (-K) K)
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc, ← abs_le]
      exact hk_abs i
    have hshrink : ∀ i, |hStep * (k i : ℝ)| ≤ |x i| := by
      intro i
      change |hStep * (if 0 ≤ x i then Int.floor (x i / hStep)
        else -Int.floor (-x i / hStep) : ℤ)| ≤ |x i|
      by_cases hxi : 0 ≤ x i
      · rw [if_pos hxi, abs_mul, abs_of_pos hStep_pos, abs_of_nonneg,
          abs_of_nonneg hxi]
        · have hlo : (Int.floor (x i / hStep) : ℝ) * hStep ≤ x i := by
            have := Int.floor_le (x i / hStep)
            rwa [le_div_iff₀ hStep_pos] at this
          nlinarith
        · exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hxi hStep_pos.le)
      · rw [if_neg hxi]
        push_cast
        rw [abs_mul, abs_of_pos hStep_pos, abs_neg, abs_of_nonneg,
          abs_of_nonpos (le_of_not_ge hxi)]
        · have hlo : (Int.floor (-x i / hStep) : ℝ) * hStep ≤ -x i := by
            have := Int.floor_le (-x i / hStep)
            rwa [le_div_iff₀ hStep_pos] at this
          nlinarith
        · exact_mod_cast Int.floor_nonneg.mpr
            (div_nonneg (neg_nonneg.mpr (le_of_not_ge hxi)) hStep_pos.le)
    have hround : ∀ i, |x i - hStep * (k i : ℝ)| ≤ hStep := by
      intro i
      change |x i - hStep * (if 0 ≤ x i then Int.floor (x i / hStep)
        else -Int.floor (-x i / hStep) : ℤ)| ≤ hStep
      by_cases hxi : 0 ≤ x i
      · rw [if_pos hxi]
        push_cast
        have hlo : (Int.floor (x i / hStep) : ℝ) * hStep ≤ x i := by
          have := Int.floor_le (x i / hStep)
          rwa [le_div_iff₀ hStep_pos] at this
        have hhi : x i < ((Int.floor (x i / hStep) : ℝ) + 1) * hStep := by
          have := Int.lt_floor_add_one (x i / hStep)
          rwa [div_lt_iff₀ hStep_pos] at this
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      · rw [if_neg hxi]
        push_cast
        have hlo : (Int.floor (-x i / hStep) : ℝ) * hStep ≤ -x i := by
          have := Int.floor_le (-x i / hStep)
          rwa [le_div_iff₀ hStep_pos] at this
        have hhi : -x i < ((Int.floor (-x i / hStep) : ℝ) + 1) * hStep := by
          have := Int.lt_floor_add_one (-x i / hStep)
          rwa [div_lt_iff₀ hStep_pos] at this
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith
    have hy_mem : b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ))) ∈
        Metric.closedBall (0 : E) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ)))‖ =
            ‖WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ))‖ := b.repr.symm.norm_map _
        _ ≤ ‖b.repr c‖ := by
          rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro i hi
          simp only [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (by simpa [hx_def] using hshrink i) 2
        _ = ‖c‖ := b.repr.norm_map c
        _ ≤ R := hc_norm
    use b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ)))
    constructor
    · change b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ))) ∈
        {y ∈ D₀ | y ∈ Metric.closedBall (0 : E) R}
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hk_in_L, hy_mem⟩
    · rw [← b.repr.isometry.dist_eq c
          (b.repr.symm (WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ)))),
        b.repr.apply_symm_apply, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
      constructor
      · positivity
      · calc
          ∑ i, ‖(b.repr c - WithLp.toLp 2 (fun i ↦ hStep * (k i : ℝ))).ofLp i‖ ^ 2
              ≤ ∑ _i : Fin n, hStep ^ 2 := by
                apply Finset.sum_le_sum
                intro i hi
                simp only [PiLp.sub_apply, Real.norm_eq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _)
                  (by simpa [hx_def] using hround i) 2
          _ = (n : ℝ) * hStep ^ 2 := by simp
          _ = (r : ℝ) ^ 2 := by
            change (n : ℝ) * ((r : ℝ) / Real.sqrt n) ^ 2 = (r : ℝ) ^ 2
            rw [div_pow, Real.sq_sqrt hn_real_pos.le]
            field_simp

/-- The dimension-dependent constant in
`FiniteDimensional.discretizeOrthonormalBasisAt`. -/
noncomputable abbrev FiniteDimensional.discretizeOrthonormalBasisAt.C
    (dim : ℕ) : NNReal :=
  ⟨(100 * (dim : ℝ) + 100) ^ (dim ^ 2), by positivity⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- Discretize the orthonormal bases of a Euclidean space at a positive scale at most one.

The exponent `dim ^ 2` comes from viewing a basis as a point of the product space `E ^ dim`;
no optimality of this exponent is asserted. -/
theorem FiniteDimensional.discretizeOrthonormalBasisAt {r : NNReal}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ D : Finset (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E),
      (D.card : NNReal) ≤
        FiniteDimensional.discretizeOrthonormalBasisAt.C (Module.finrank ℝ E) *
          r⁻¹ ^ (Module.finrank ℝ E) ^ 2 ∧
      ∀ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
        ∃ b' ∈ D, ∀ i, ‖b i - b' i‖ ≤ r := by
  classical
  let n := finrank ℝ E
  change ∃ D : Finset (OrthonormalBasis (Fin n) ℝ E),
    (D.card : NNReal) ≤ FiniteDimensional.discretizeOrthonormalBasisAt.C n *
      r⁻¹ ^ n ^ 2 ∧
    ∀ b : OrthonormalBasis (Fin n) ℝ E, ∃ b' ∈ D, ∀ i, ‖b i - b' i‖ ≤ r
  let ε : NNReal := r / 2
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    exact (div_le_self zero_le (by norm_num)).trans hr1
  have hεinv : 1 / ε = 2 * r⁻¹ := by
    simp [ε, div_eq_mul_inv, mul_inv_rev]
  obtain ⟨V, hVcard, _, hVnet⟩ :=
    FiniteDimensional.discretizeBallAt (E := E) hε hε1
  let codes : Finset (Fin n → E) := Fintype.piFinset fun _ ↦ V
  let occupied := {v ∈ codes |
    ∃ b : OrthonormalBasis (Fin n) ℝ E, ∀ i, dist (b i) (v i) ≤ ε}
  let rep : {v // v ∈ occupied} → OrthonormalBasis (Fin n) ℝ E := fun v ↦
    Classical.choose (Finset.mem_filter.mp v.property).2
  let D : Finset (OrthonormalBasis (Fin n) ℝ E) := occupied.attach.image rep
  have hDcard : D.card ≤ V.card ^ n := by
    calc
      D.card ≤ occupied.attach.card := by
        dsimp [D]
        exact Finset.card_image_le
      _ = occupied.card := Finset.card_attach
      _ ≤ codes.card := by
        dsimp [occupied]
        exact Finset.card_filter_le _ _
      _ = V.card ^ n := by simp [codes, Fintype.card_piFinset]
  let A : NNReal := 100 * n + 100
  have hn : 0 < n := finrank_pos
  have hsqrt : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]⟩
  have hbase : (4 * NNReal.sqrt n + 5) * 2 ≤ A := by
    rw [← NNReal.coe_le_coe]
    push_cast
    dsimp [A]
    push_cast
    nlinarith
  have hVcard' : (V.card : NNReal) ≤ (A * r⁻¹) ^ n := by
    calc
      (V.card : NNReal) ≤ FiniteDimensional.discretizeBallAt.C n * (1 / ε) ^ n := hVcard
      _ = ((4 * NNReal.sqrt n + 5) * 2 * r⁻¹) ^ n := by
        rw [hεinv]
        simp only [FiniteDimensional.discretizeBallAt.C, mul_pow]
        ring
      _ ≤ (A * r⁻¹) ^ n := by gcongr
  have hC : FiniteDimensional.discretizeOrthonormalBasisAt.C n = A ^ (n ^ 2) := by
    apply NNReal.eq
    change (100 * (n : ℝ) + 100) ^ (n ^ 2) = _
    simp [A]
  have hcard : (D.card : NNReal) ≤
      FiniteDimensional.discretizeOrthonormalBasisAt.C n * r⁻¹ ^ n ^ 2 := by
    calc
      (D.card : NNReal) ≤ ((V.card ^ n : ℕ) : NNReal) := by exact_mod_cast hDcard
      _ = (V.card : NNReal) ^ n := by norm_cast
      _ ≤ ((A * r⁻¹) ^ n) ^ n := by gcongr
      _ = A ^ (n ^ 2) * r⁻¹ ^ (n ^ 2) := by
        simp only [mul_pow, ← pow_mul, pow_two]
      _ = FiniteDimensional.discretizeOrthonormalBasisAt.C n * r⁻¹ ^ n ^ 2 := by
        rw [hC]
  refine ⟨D, hcard, ?_⟩
  intro b
  choose v hvV hvdist using fun i ↦ hVnet (b i) (by simp [Metric.mem_closedBall])
  have hvcode : v ∈ codes := by
    change v ∈ Fintype.piFinset fun _ : Fin n ↦ V
    rw [Fintype.mem_piFinset]
    exact hvV
  have hvocc : v ∈ occupied := by
    change v ∈ {v ∈ codes |
      ∃ b : OrthonormalBasis (Fin n) ℝ E, ∀ i, dist (b i) (v i) ≤ ε}
    rw [Finset.mem_filter]
    exact ⟨hvcode, ⟨b, hvdist⟩⟩
  let v' : {v // v ∈ occupied} := ⟨v, hvocc⟩
  refine ⟨rep v', ?_, ?_⟩
  · change rep v' ∈ occupied.attach.image rep
    exact Finset.mem_image_of_mem rep (by simp [v'])
  · intro i
    have hrep : ∀ i, dist (rep v' i) (v i) ≤ ε := by
      exact Classical.choose_spec (Finset.mem_filter.mp v'.property).2
    rw [← dist_eq_norm]
    calc
      dist (b i) (rep v' i) ≤ dist (b i) (v i) + dist (v i) (rep v' i) :=
        dist_triangle _ _ _
      _ ≤ (ε : ℝ) + ε := add_le_add (hvdist i) (by simpa [dist_comm] using hrep i)
      _ = (r : ℝ) := by norm_num [ε]

/-- A dimension-dependent constant for the discretization of bounded rectangular prisms. -/
@[nolint defsWithUnderscore]
noncomputable abbrev exists_bounded_prism_discretization.C (n : ℕ) : NNReal :=
  ⟨(100 * (n : ℝ) + 100) ^ (n ^ 4 + n ^ 3 + n + 1), by positivity⟩

/-- The exponent in the cardinality bound for the discretization of bounded rectangular
prisms. -/
@[nolint defsWithUnderscore]
abbrev exists_bounded_prism_discretization.M (n : ℕ) : ℝ :=
  n ^ 4 + n ^ 3 + n + 1

/-- The dimensional volume-comparison factor in the bounded-prism discretization. -/
@[nolint defsWithUnderscore]
noncomputable abbrev exists_bounded_prism_discretization.volumeFactor (n : ℕ) : NNReal :=
  (2 * PrismNDim.perturbation_subset_dilation.C n) ^ n

/-- The dimensional part of the localization radius in the bounded-prism discretization. -/
@[nolint defsWithUnderscore]
noncomputable abbrev exists_bounded_prism_discretization.localizationRadius
    (n : ℕ) : NNReal :=
  n * PrismNDim.perturbation_subset_dilation.C n

/-- The prism-discretization constant is positive. -/
lemma exists_bounded_prism_discretization.C_pos (n : ℕ) : 0 < C n := by
  rw [← NNReal.coe_pos]
  change (0 : ℝ) < (100 * (n : ℝ) + 100) ^ (n ^ 4 + n ^ 3 + n + 1)
  positivity

/-- The prism-discretization exponent is positive. -/
lemma exists_bounded_prism_discretization.M_pos (n : ℕ) : 0 < M n := by
  positivity

/-- **Polynomial-size discretization of bounded rectangular prisms.**

At every positive scale `r`, there is a finite family of bounded rectangular prisms such that
every prism with controlled center and half-widths between `r` and `1` is contained in a member
of the family. The containing prism has volume bounded by a dimensional constant times the
original volume.
-/
theorem exists_bounded_prism_discretization {r R : NNReal} (hr : 0 < r) (hR : 1 ≤ R) :
    ∃ QTest : Finset (PrismNDim (finrank ℝ E) E E),
      (QTest.card : NNReal) ≤
          exists_bounded_prism_discretization.C (finrank ℝ E) *
            R ^ finrank ℝ E *
              r ^ (-exists_bounded_prism_discretization.M (finrank ℝ E)) ∧
      (∀ Q ∈ QTest, Q.carrier ⊆ Metric.closedBall (0 : E)
        ((R : ℝ) +
          exists_bounded_prism_discretization.localizationRadius (finrank ℝ E))) ∧
      ∀ P : PrismNDim (finrank ℝ E) E E,
        P.center ∈ Metric.closedBall (0 : E) R →
        (∀ i, r ≤ P.thicknesses i) →
        (∀ i, P.thicknesses i ≤ 1) →
        ∃ Q ∈ QTest, P.carrier ⊆ Q.carrier ∧
          volume Q.carrier ≤
            exists_bounded_prism_discretization.volumeFactor (finrank ℝ E) *
              volume P.carrier := by
  classical
  let n := finrank ℝ E
  change ∃ QTest : Finset (PrismNDim n E E),
    (QTest.card : NNReal) ≤ exists_bounded_prism_discretization.C n * R ^ n *
      r ^ (-exists_bounded_prism_discretization.M n) ∧
    (∀ Q ∈ QTest, Q.carrier ⊆ Metric.closedBall (0 : E)
      ((R : ℝ) + exists_bounded_prism_discretization.localizationRadius n)) ∧
    ∀ P : PrismNDim n E E,
      P.center ∈ Metric.closedBall (0 : E) R →
      (∀ i, r ≤ P.thicknesses i) →
      (∀ i, P.thicknesses i ≤ 1) →
      ∃ Q ∈ QTest, P.carrier ⊆ Q.carrier ∧
        volume Q.carrier ≤ exists_bounded_prism_discretization.volumeFactor n * volume P.carrier
  have hn : 0 < n := finrank_pos
  by_cases hr1 : r ≤ 1
  swap
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro P _ hlow hupp
    exact (hr1 ((hlow ⟨0, hn⟩).trans (hupp ⟨0, hn⟩))).elim
  obtain ⟨centers, hcenters_card, hcenters_mem, hcenters_net⟩ :=
    FiniteDimensional.discretizeBallAt (E := E) hr (hr1.trans hR)
  obtain ⟨bases, hbases_card, hbases_net⟩ :=
    FiniteDimensional.discretizeOrthonormalBasisAt (E := E) hr hr1
  set K : ℕ := Nat.ceil ((r : ℝ)⁻¹) with hKdef
  have hK_bound : (K : ℝ) ≤ 2 * (r : ℝ)⁻¹ := by
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
    have hone : (1 : ℝ) ≤ (r : ℝ)⁻¹ := (one_le_inv₀ hr').mpr hr1'
    have hceil := Nat.ceil_lt_add_one (inv_nonneg.mpr hr'.le)
    rw [← hKdef] at hceil
    linarith
  set widthIndices : Finset (Fin n → ℕ) :=
    Fintype.piFinset (fun _ : Fin n ↦ Finset.Icc 1 K) with hwidthIndices
  set data := (centers.product bases).product widthIndices with hdata
  set QTest : Finset (PrismNDim n E E) := data.image fun d ↦
    (PrismNDim.mk' d.1.1 d.1.2 (fun i ↦ min (d.2 i * r) 1)).dilation
      (PrismNDim.perturbation_subset_dilation.C n) with hQTest
  refine ⟨QTest, ?_, ?_, ?_⟩
  · have hwidthIndices_card : (widthIndices.card : NNReal) ≤ (2 * r⁻¹) ^ n := by
      calc
        (widthIndices.card : NNReal) ≤ (K ^ n : ℕ) := by
          exact_mod_cast (show widthIndices.card ≤ K ^ n by
            rw [hwidthIndices]
            simp [Fintype.card_piFinset])
        _ = (K : NNReal) ^ n := by norm_cast
        _ ≤ (2 * r⁻¹) ^ n := by
          gcongr
          rw [← NNReal.coe_le_coe]
          push_cast
          exact hK_bound
    calc
      (QTest.card : NNReal) ≤ data.card := by
        rw [hQTest]
        exact_mod_cast Finset.card_image_le
      _ = (centers.card : NNReal) * bases.card * widthIndices.card := by
        rw [hdata]
        norm_cast
        simp
      _ ≤ (FiniteDimensional.discretizeBallAt.C n * (R / r) ^ n) *
          (FiniteDimensional.discretizeOrthonormalBasisAt.C n * r⁻¹ ^ n ^ 2) *
            ((2 * r⁻¹) ^ n) := by gcongr
      _ ≤ exists_bounded_prism_discretization.C n * R ^ n *
          r ^ (-exists_bounded_prism_discretization.M n) := by
        let A : NNReal := 100 * n + 100
        let m := n ^ 4 + n ^ 3 + n + 1
        have hm_const : 2 * n + 2 * n ^ 2 ≤ m := by
          dsimp [m]
          nlinarith [sq_nonneg (n ^ 2 - n : ℤ)]
        have hm : n + n ^ 2 ≤ m :=
          (by omega : n + n ^ 2 ≤ 2 * n + 2 * n ^ 2).trans hm_const
        have hm_r : n ^ 2 + 2 * n ≤ m :=
          (by omega : n ^ 2 + 2 * n ≤ 2 * n + 2 * n ^ 2).trans hm_const
        have hsqrt : Real.sqrt n ≤ n := by
          rw [Real.sqrt_le_iff]
          exact ⟨by positivity, by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]⟩
        have hsmall : (4 * NNReal.sqrt n + 5) * 2 ≤ A := by
          rw [← NNReal.coe_le_coe]
          push_cast
          dsimp [A]
          push_cast
          nlinarith
        have hA_one : 1 ≤ A := by
          change (1 : NNReal) ≤ 100 * n + 100
          exact le_trans (by norm_num : (1 : NNReal) ≤ 100)
            (le_add_of_nonneg_left (mul_nonneg zero_le zero_le))
        have hconst : ((4 * NNReal.sqrt n + 5) * 2) ^ n * A ^ (n ^ 2) ≤ A ^ m := by
          calc
            ((4 * NNReal.sqrt n + 5) * 2) ^ n * A ^ (n ^ 2)
                ≤ A ^ n * A ^ (n ^ 2) := by gcongr
            _ = A ^ (n + n ^ 2) := (pow_add A n (n ^ 2)).symm
            _ ≤ A ^ m := (pow_right_mono₀ hA_one) hm
        have hr_inv_one : (1 : NNReal) ≤ r⁻¹ := by
          rw [← inv_one]
          exact (inv_le_inv₀ zero_lt_one hr).mpr hr1
        have hr_power : r⁻¹ ^ (n ^ 2 + 2 * n) ≤ r⁻¹ ^ m :=
          (pow_right_mono₀ hr_inv_one) hm_r
        have hbasisC : FiniteDimensional.discretizeOrthonormalBasisAt.C n =
            A ^ (n ^ 2) := rfl
        have hrewrite :
            (FiniteDimensional.discretizeBallAt.C n * (R / r) ^ n) *
                (FiniteDimensional.discretizeOrthonormalBasisAt.C n * r⁻¹ ^ n ^ 2) *
                  (2 * r⁻¹) ^ n =
              R ^ n * ((4 * NNReal.sqrt n + 5) * 2) ^ n *
                A ^ (n ^ 2) * r⁻¹ ^ (n ^ 2 + 2 * n) := by
          rw [hbasisC]
          dsimp only [FiniteDimensional.discretizeBallAt.C]
          simp only [div_eq_mul_inv, mul_pow]
          rw [show n ^ 2 + 2 * n = n + n ^ 2 + n by omega]
          simp only [pow_add]
          ring
        have hC : exists_bounded_prism_discretization.C n = A ^ m := by
          apply NNReal.eq
          change (100 * (n : ℝ) + 100) ^ (n ^ 4 + n ^ 3 + n + 1) = _
          simp [A, m]
        have hrpow : r ^ (-exists_bounded_prism_discretization.M n) = r⁻¹ ^ m := by
          rw [show exists_bounded_prism_discretization.M n = (m : ℝ) by simp [m],
            NNReal.rpow_neg, NNReal.rpow_natCast]
          exact (inv_pow r m).symm
        rw [hrewrite, hC, hrpow]
        calc
          R ^ n * ((4 * NNReal.sqrt n + 5) * 2) ^ n * A ^ (n ^ 2) *
                r⁻¹ ^ (n ^ 2 + 2 * n)
              = R ^ n * (((4 * NNReal.sqrt n + 5) * 2) ^ n *
                  A ^ (n ^ 2)) * r⁻¹ ^ (n ^ 2 + 2 * n) := by ring
          _ ≤ R ^ n * A ^ m * r⁻¹ ^ m := by gcongr
          _ = A ^ m * R ^ n * r⁻¹ ^ m := by ring
  · intro Q hQ
    rw [hQTest, Finset.mem_image] at hQ
    obtain ⟨⟨⟨c, b⟩, k⟩, hd, rfl⟩ := hQ
    rcases Finset.mem_product.mp (show ((c, b), k) ∈
      (centers.product bases).product widthIndices by simpa only [hdata] using hd) with ⟨hcb, _⟩
    have hcball := hcenters_mem c (Finset.mem_product.mp hcb).1
    intro x hx
    have hxball := ((PrismNDim.mk' c b (fun i ↦ min (k i * r) 1)).dilation
      (PrismNDim.perturbation_subset_dilation.C n)).carrier_subset_closedBall hx
    rw [Metric.mem_closedBall, dist_eq_norm_vsub E] at hxball
    simp only [PrismNDim.dilation, PrismNDim.center_mk', PrismNDim.thicknesses_mk'] at hxball
    have hsum :
        (∑ i, ((PrismNDim.perturbation_subset_dilation.C n *
          min (k i * r) 1 : NNReal) : ℝ)) ≤
            exists_bounded_prism_discretization.localizationRadius n := by
      calc
        (∑ i, ((PrismNDim.perturbation_subset_dilation.C n *
              min (k i * r) 1 : NNReal) : ℝ)) ≤
            ∑ _i : Fin n, (PrismNDim.perturbation_subset_dilation.C n : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ by
            exact_mod_cast mul_le_of_le_one_right
              (PrismNDim.perturbation_subset_dilation.C n).coe_nonneg (min_le_right _ _)
        _ = (exists_bounded_prism_discretization.localizationRadius n : ℝ) := by
          simp [exists_bounded_prism_discretization.localizationRadius, Finset.sum_const,
            nsmul_eq_mul]
          ring
    have hxball' : ‖x -ᵥ c‖ ≤
        exists_bounded_prism_discretization.localizationRadius n := hxball.trans (by
      simpa only [PrismNDim.thicknesses_mk'] using hsum)
    rw [Metric.mem_closedBall, dist_zero_right] at hcball ⊢
    calc
      ‖x‖ ≤ ‖x -ᵥ c‖ + ‖c‖ := by simpa [vsub_eq_sub] using norm_add_le (x - c) c
      _ ≤ exists_bounded_prism_discretization.localizationRadius n + R :=
        add_le_add hxball' (by exact_mod_cast hcball)
      _ = (R : ℝ) + exists_bounded_prism_discretization.localizationRadius n := add_comm _ _
  · intro P hPcenter hPlow hPupp
    obtain ⟨c, hc, hPc⟩ := hcenters_net P.center hPcenter
    obtain ⟨b, hb, hPb⟩ := hbases_net P.basis
    let k : Fin n → ℕ := fun i ↦ Nat.ceil ((P.thicknesses i : ℝ) / r)
    have hk : k ∈ widthIndices := by
      rw [hwidthIndices, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      constructor
      · rw [Nat.one_le_ceil_iff]
        exact div_pos (by exact_mod_cast hr.trans_le (hPlow i)) (by exact_mod_cast hr)
      · rw [hKdef]
        apply Nat.ceil_mono
        have hi : (P.thicknesses i : ℝ) ≤ 1 := by exact_mod_cast hPupp i
        simpa only [one_div] using
          div_le_div_of_nonneg_right hi (show (0 : ℝ) ≤ r by positivity)
    let S : PrismNDim n E E := PrismNDim.mk' c b (fun i ↦ min (k i * r) 1)
    let Q : PrismNDim n E E := S.dilation (PrismNDim.perturbation_subset_dilation.C n)
    have hQ : Q ∈ QTest := by
      rw [hQTest]
      exact Finset.mem_image.mpr ⟨((c, b), k), by
        rw [hdata]
        exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc, hb⟩, hk⟩, rfl⟩
    refine ⟨Q, hQ, ?_, ?_⟩
    · have hS_lower : ∀ i, r ≤ S.thicknesses i := by
        intro i
        change r ≤ min (k i * r) 1
        refine le_min ?_ hr1
        calc
          r = 1 * r := by simp
          _ ≤ (k i : NNReal) * r := by
            gcongr
            exact_mod_cast (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hk) i)).1
      have hS_upper : ∀ i, S.thicknesses i ≤ 1 := fun _ ↦ min_le_right _ _
      have hpert : S.IsRPerturbation P r := by
        refine ⟨hPc, ?_, ?_⟩
        · intro i
          exact (norm_sub_rev (b i) (P.basis i)).symm ▸ hPb i
        · intro i
          change P.thicknesses i ≤ min (k i * r) 1
          refine le_min ?_ (hPupp i)
          have hceil : (P.thicknesses i : ℝ) / r ≤ k i := Nat.le_ceil _
          rw [div_le_iff₀ (by exact_mod_cast hr)] at hceil
          exact_mod_cast hceil
      simpa only [Q] using S.perturbation_subset_dilation P hS_lower hS_upper hpert
    · have hwidth : ∀ i, min (k i * r) 1 ≤ 2 * P.thicknesses i := by
        intro i
        refine (min_le_left _ _).trans ?_
        rw [← NNReal.coe_le_coe]
        push_cast
        have hceil := Nat.ceil_lt_add_one
          (show (0 : ℝ) ≤ (P.thicknesses i : ℝ) / r by positivity)
        have hr' : (0 : ℝ) < r := by exact_mod_cast hr
        have hmul := mul_lt_mul_of_pos_right hceil hr'
        have hdiv : (P.thicknesses i : ℝ) / r * r = P.thicknesses i := by
          field_simp
        have hri : (r : ℝ) ≤ P.thicknesses i := by exact_mod_cast hPlow i
        dsimp [k]
        nlinarith
      simp only [Q, S]
      rw [PrismNDim.volume_carrier, PrismNDim.volume_carrier]
      have hprod :
          ∏ i, ((PrismNDim.perturbation_subset_dilation.C n *
              min (k i * r) 1 : NNReal) : ENNReal) ≤
            ∏ i, ((2 * PrismNDim.perturbation_subset_dilation.C n : NNReal) : ENNReal) *
              P.thicknesses i := by
        apply Finset.prod_le_prod (fun _ _ ↦ zero_le)
        intro i _
        exact_mod_cast (mul_le_mul_right (hwidth i)
          (PrismNDim.perturbation_subset_dilation.C n)).trans_eq (by ring)
      calc
        2 ^ n * ∏ i, ((PrismNDim.perturbation_subset_dilation.C n *
              min (k i * r) 1 : NNReal) : ENNReal)
            ≤ 2 ^ n * ∏ i,
                ((2 * PrismNDim.perturbation_subset_dilation.C n : NNReal) : ENNReal) *
                  P.thicknesses i :=
          mul_le_mul_right hprod _
        _ = (exists_bounded_prism_discretization.volumeFactor n : ENNReal) *
            (2 ^ n * ∏ i, (P.thicknesses i : ENNReal)) := by
          simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, exists_bounded_prism_discretization.volumeFactor]
          push_cast
          ring

/-- A dimension-dependent constant for discretizing convex bodies by rectangular prisms. -/
@[nolint defsWithUnderscore]
noncomputable abbrev exists_volume_bounded_prism_discretization.C (n : ℕ) : NNReal :=
  max
    (max (exists_bounded_prism_discretization.C n * ((n + 1 : ℕ) : NNReal) ^ n)
      (((n + 1 : ℕ) : NNReal) + exists_bounded_prism_discretization.localizationRadius n))
    (exists_bounded_prism_discretization.volumeFactor n *
      max 1 (Metric.volume_comparison.C n))

/-- The exponent in the cardinality bound for the discretization of convex bodies by
rectangular prisms. -/
@[nolint defsWithUnderscore]
abbrev exists_volume_bounded_prism_discretization.M (n : ℕ) : ℝ :=
  exists_bounded_prism_discretization.M n

/-- The convex-body discretization constant is positive. -/
lemma exists_volume_bounded_prism_discretization.C_pos (n : ℕ) : 0 < C n := by
  exact lt_of_lt_of_le
    (mul_pos (exists_bounded_prism_discretization.C_pos n) (pow_pos (by positivity) n))
    ((le_max_left _ _).trans (le_max_left _ _))

/-- The convex-body discretization exponent is positive. -/
lemma exists_volume_bounded_prism_discretization.M_pos (n : ℕ) : 0 < M n := by
  exact exists_bounded_prism_discretization.M_pos n

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A lower bound on the smallest affine thickness (`ethickness.scale`) bounds the affine
thickness at every rank below the dimension from below. -/
lemma exists_volume_bounded_prism_discretization.thickness_ge_of_le_scale
    {r : NNReal} {s : Set E} (hs : Bornology.IsBounded s)
    (hscale : r ≤ Metric.ethickness.scale ℝ s) (i : Fin (finrank ℝ E)) :
    (r : ℝ) ≤ Metric.thickness ℝ s (i : ℕ) := by
  have h1 : (r : ENNReal) ≤ Metric.ethickness ℝ s (i : ℕ) :=
    (Metric.ethickness.le_scale_iff s).mp hscale i
  rw [Metric.ethickness_thickness' hs (i : ℕ), ← ENNReal.ofReal_coe_nnreal] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg s (i : ℕ))).mp h1

/-- The localization radius from the bounded-prism discretization is dominated by the
convex-body discretization constant. -/
lemma exists_volume_bounded_prism_discretization.localization_radius_le (n : ℕ) :
    (n : ℝ) + 1 + exists_bounded_prism_discretization.localizationRadius n ≤
      (exists_volume_bounded_prism_discretization.C n : ℝ) := by
  have hle : ((n + 1 : ℕ) : NNReal) + exists_bounded_prism_discretization.localizationRadius n ≤
      exists_volume_bounded_prism_discretization.C n :=
    (le_max_right _ _).trans (le_max_left _ _)
  calc
    (n : ℝ) + 1 + exists_bounded_prism_discretization.localizationRadius n =
        ((((n + 1 : ℕ) : NNReal) +
          exists_bounded_prism_discretization.localizationRadius n : NNReal) : ℝ) := by
      push_cast
      ring
    _ ≤ (exists_volume_bounded_prism_discretization.C n : ℝ) := by exact_mod_cast hle

/-- The product of the prism volume factor and the outer-prism volume-comparison constant is
dominated by the convex-body discretization constant. -/
lemma exists_volume_bounded_prism_discretization.volumeFactor_mul_volume_comparison_le (n : ℕ) :
    exists_bounded_prism_discretization.volumeFactor n * Metric.volume_comparison.C n
      ≤ exists_volume_bounded_prism_discretization.C n := by
  calc
    exists_bounded_prism_discretization.volumeFactor n * Metric.volume_comparison.C n
        ≤ exists_bounded_prism_discretization.volumeFactor n *
            max 1 (Metric.volume_comparison.C n) := by
      gcongr
      exact le_max_right _ _
    _ ≤ exists_volume_bounded_prism_discretization.C n := le_max_right _ _

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The outer prism of a convex body inside the closed unit ball has its center within distance
`n + 1` of the origin. -/
lemma exists_volume_bounded_prism_discretization.outerPrism_center_mem
    {K : ConvexSpaceBody E} (hK : K.carrier ⊆ Metric.closedBall (0 : E) 1) :
    (outerPrism (n := finrank ℝ E) rfl K.isCompact' K.nonempty').center
      ∈ Metric.closedBall (0 : E) ((finrank ℝ E : ℝ) + 1) := by
  set P := outerPrism (n := finrank ℝ E) rfl K.isCompact' K.nonempty' with hPdef
  obtain ⟨p, hp⟩ := K.nonempty'
  have hp1 : dist p 0 ≤ 1 := by simpa [Metric.mem_closedBall] using hK hp
  have hpP : p ∈ P.carrier := by
    rw [hPdef]; exact outerPrism.self_subset (n := finrank ℝ E) rfl K.isCompact' K.nonempty' hp
  have hpc : dist p P.center ≤ ∑ i, (P.thicknesses i : ℝ) := by
    simpa [Metric.mem_closedBall] using PrismNDim.carrier_subset_closedBall P hpP
  have hle : ∀ i, (P.thicknesses i : ℝ) ≤ 1 := by
    intro i
    rw [hPdef, outerPrism.thicknesses_eq rfl K.isCompact' K.nonempty' i]
    exact Metric.thickness_le_of_subset_closedBall hK (by norm_num) (i : ℕ)
  have hsum : (∑ i, (P.thicknesses i : ℝ)) ≤ (finrank ℝ E : ℝ) := by
    calc (∑ i, (P.thicknesses i : ℝ)) ≤ ∑ _i : Fin (finrank ℝ E), (1:ℝ) :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ = (finrank ℝ E : ℝ) := by simp
  simp only [Metric.mem_closedBall]
  calc dist P.center 0 ≤ dist P.center p + dist p 0 := dist_triangle _ _ _
    _ = dist p P.center + dist p 0 := by rw [dist_comm]
    _ ≤ (finrank ℝ E : ℝ) + 1 := by linarith [hpc, hp1, hsum]

/-- **Polynomial-size discretization of convex bodies by rectangular prisms.**

At every positive scale `r`, there is a polynomial-size finite family of rectangular prisms such
that every convex body in the closed unit ball with smallest affine thickness at least `r` is
contained in a member of the family whose volume is bounded by a dimensional constant times the
body's volume.
-/
theorem exists_volume_bounded_prism_discretization {r : NNReal} (hr : 0 < r) :
    ∃ QTest : Finset (PrismNDim (finrank ℝ E) E E),
      (QTest.card : NNReal) ≤
          exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
            r ^ (-exists_volume_bounded_prism_discretization.M (finrank ℝ E)) ∧
      (∀ Q ∈ QTest, Q.carrier ⊆ Metric.closedBall (0 : E)
        (exists_volume_bounded_prism_discretization.C (finrank ℝ E) : ℝ)) ∧
      ∀ K : ConvexSpaceBody E, K.carrier ⊆ Metric.closedBall (0 : E) 1 →
        r ≤ Metric.ethickness.scale ℝ K.carrier →
        ∃ Q ∈ QTest, K.carrier ⊆ Q.carrier ∧
          volume Q.carrier ≤
            (exists_volume_bounded_prism_discretization.C (finrank ℝ E) : ENNReal) *
              volume K.carrier := by
  set n := finrank ℝ E
  set R : NNReal := (n : ℕ) + 1 with hRdef
  have hR : 1 ≤ R := by dsimp [R]; exact_mod_cast Nat.le_add_left 1 n
  have hprism : ∃ QTest : Finset (PrismNDim n E E),
    (QTest.card : NNReal) ≤
      exists_bounded_prism_discretization.C n * R ^ n *
        r ^ (-exists_bounded_prism_discretization.M n) ∧
    (∀ Q ∈ QTest, Q.carrier ⊆ Metric.closedBall (0 : E)
      ((R : ℝ) + exists_bounded_prism_discretization.localizationRadius n)) ∧
    ∀ P : PrismNDim n E E,
      P.center ∈ Metric.closedBall (0 : E) (R : ℝ) →
      (∀ i : Fin n, r ≤ P.thicknesses i) →
      (∀ i : Fin n, P.thicknesses i ≤ 1) →
      ∃ Q ∈ QTest, P.carrier ⊆ Q.carrier ∧
        volume Q.carrier ≤
          exists_bounded_prism_discretization.volumeFactor n * volume P.carrier :=
    exists_bounded_prism_discretization (E := E) hr hR
  rcases hprism with ⟨QTest, hcard, hloc, hprism⟩
  refine ⟨QTest, ?_, ?_, ?_⟩
  · -- cardinality bound
    have hprod : exists_bounded_prism_discretization.C n * R ^ n
        ≤ exists_volume_bounded_prism_discretization.C n := by
      have hRpow : R ^ n = ((n + 1 : ℕ) : NNReal) ^ n := by simp [R]
      rw [hRpow]
      exact (le_max_left _ _).trans (le_max_left _ _)
    calc (QTest.card : NNReal)
        ≤ exists_bounded_prism_discretization.C n * R ^ n *
            r ^ (-exists_bounded_prism_discretization.M n) := hcard
      _ ≤ exists_volume_bounded_prism_discretization.C n *
            r ^ (-exists_volume_bounded_prism_discretization.M n) := mul_le_mul' hprod le_rfl
  · -- localization radius
    intro Q hQ
    refine (hloc Q hQ).trans (Metric.closedBall_subset_closedBall ?_)
    change (n : ℝ) + 1 + exists_bounded_prism_discretization.localizationRadius n ≤ _
    exact exists_volume_bounded_prism_discretization.localization_radius_le n
  · -- main property
    intro K hK hscale
    have hKcv : Convex ℝ K.carrier := K.convex
    have hKc : IsCompact K.carrier := K.isCompact'
    have hKne : K.carrier.Nonempty := K.nonempty'
    have hKbdd : Bornology.IsBounded K.carrier := hKc.isBounded
    set P := outerPrism (n := n) rfl hKc hKne with hPdef
    have hcenter : P.center ∈ Metric.closedBall (0 : E) (R : ℝ) := by
      rw [hRdef, show (R : ℝ) = (n : ℝ) + 1 by simp [R]]
      exact exists_volume_bounded_prism_discretization.outerPrism_center_mem hK
    have hthick_eq : ∀ i : Fin n, (P.thicknesses i : ℝ) = Metric.thickness ℝ K.carrier (i : ℕ) := by
      intro i
      rw [hPdef, outerPrism.thicknesses_eq rfl hKc hKne i]; rfl
    have hthick_ge : ∀ i : Fin n, r ≤ P.thicknesses i := fun i => by
      exact_mod_cast (exists_volume_bounded_prism_discretization.thickness_ge_of_le_scale
        hKbdd hscale i).trans_eq (hthick_eq i).symm
    have hthick_le_1 : ∀ i : Fin n, P.thicknesses i ≤ 1 := fun i => by
      have : (P.thicknesses i : ℝ) ≤ 1 := by
        rw [hthick_eq i]; exact Metric.thickness_le_of_subset_closedBall hK (by norm_num) (i : ℕ)
      exact_mod_cast this
    rcases hprism P hcenter hthick_ge hthick_le_1 with ⟨Q, hQ, hPcarrier, hVol⟩
    refine ⟨Q, hQ, ?_, ?_⟩
    · exact (outerPrism.self_subset (n := n) rfl hKc hKne).trans hPcarrier
    · -- volume bound
      calc
        volume Q.carrier ≤
            exists_bounded_prism_discretization.volumeFactor n * volume P.carrier := hVol
        _ = (exists_bounded_prism_discretization.volumeFactor n : ENNReal) *
            volume (outerPrism (n := n) rfl hKc hKne).carrier := by
          simp [hPdef]
        _ ≤ (exists_bounded_prism_discretization.volumeFactor n : ENNReal) *
            ((Metric.volume_comparison.C n : ENNReal) * volume K.carrier) := by
          gcongr
          exact Metric.volume_outerPrism_le_volume_self (n := n) rfl hKcv hKc hKne
        _ = (exists_bounded_prism_discretization.volumeFactor n *
            Metric.volume_comparison.C n : ENNReal) * volume K.carrier := by simp [mul_assoc]
        _ ≤ (exists_volume_bounded_prism_discretization.C n : ENNReal) * volume K.carrier := by
          have hle : exists_bounded_prism_discretization.volumeFactor n *
              Metric.volume_comparison.C n
              ≤ exists_volume_bounded_prism_discretization.C n :=
            exists_volume_bounded_prism_discretization.volumeFactor_mul_volume_comparison_le n
          exact mul_le_mul_left (by exact_mod_cast hle) _

/-- **Finite prism test family for the maximal density.**

At every scale `0 < r < 1` there is a finite family of rectangular prisms, of cardinality at most
`C * r ^ (-M)` and depending only on `r`, that recovers the maximal density of any finite family of
convex bodies (each contained in the closed unit ball and with smallest affine thickness at least
`r`) up to the dimensional constant `C`: some prism `Q` in the family satisfies
`maxDensity s W ≤ C * densityIn s W Q`.
-/
theorem exists_finite_test_family_maxDensity {r : NNReal} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ QTest : Finset (PrismNDim (finrank ℝ E) E E),
      (QTest.card : NNReal) ≤
          exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
            r ^ (- exists_volume_bounded_prism_discretization.M (finrank ℝ E)) ∧
      ∀ {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E),
        (∀ i ∈ s, (W i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (∀ i ∈ s, r ≤ Metric.ethickness.scale ℝ (W i).carrier) →
        ∃ Q ∈ QTest, maxDensity s W ≤
          (exists_volume_bounded_prism_discretization.C (finrank ℝ E) : ENNReal) *
            densityIn s W Q.toConvexSpaceBody := by
  set n := finrank ℝ E with hn
  obtain ⟨QTest, hcard, _, hmain⟩ := exists_volume_bounded_prism_discretization (E := E) hr
  refine ⟨QTest, hcard, ?_⟩
  intro ι s W hball hthick
  set J := density_maximizer s W
  set Kstar := J.convexHull_biUnion W
  have h_max_eq : maxDensity s W = densityIn s W Kstar := by
    symm
    exact densityIn_self_maximizer_eq s W
  by_cases hJempty : J = ∅
  · -- Empty maximizer: the maximal density vanishes; the closed unit ball supplies a `Q ∈ QTest`.
    have hmax0 : maxDensity s W = 0 :=
      maxDensity_eq_zero_of_maximizer_eq_empty hJempty
    have hball_carrier : (ConvexSpaceBody.closedUnitBall (E := E)).carrier
        ⊆ Metric.closedBall (0 : E) 1 := by
      simp
    have hscale_ball : r ≤ Metric.ethickness.scale ℝ
        (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
      dsimp [ConvexSpaceBody.closedUnitBall]
      have h_scale_eq : Metric.ethickness.scale ℝ (Metric.closedBall (0 : E) 1) =
          Metric.ethickness ℝ (Metric.closedBall (0 : E) 1) (n - 1) :=
        Metric.ethickness.scale_eq (Metric.closedBall (0 : E) 1)
      rw [h_scale_eq]
      trans (1 : ENNReal)
      · exact_mod_cast hr1
      · have hn_sub1_lt_finrank : n - 1 < Module.finrank ℝ E := by
          rw [hn]
          exact Nat.sub_one_lt (Module.finrank_pos (R := ℝ) (M := E)).ne'
        simpa using le_ethickness_closedBall (x := (0 : E)) (r := 1) (n := n - 1) hn_sub1_lt_finrank
    rcases hmain ConvexSpaceBody.closedUnitBall hball_carrier hscale_ball with ⟨Q, hQ, _, _⟩
    refine ⟨Q, hQ, ?_⟩
    rw [hmax0]
    exact zero_le
  · -- Nonempty maximizer: apply the discretization to the maximizing body `Kstar`.
    have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJempty
    have hKstar_carrier : Kstar.carrier ⊆ Metric.closedBall (0 : E) 1 := by
      apply (hJne.convexHull_biUnion_le_iff W (ConvexSpaceBody.closedUnitBall (E := E))).mpr
      intro i hi
      apply hball
      exact density_maximizer_subset s W hi
    obtain ⟨j, hj⟩ := hJne
    have hJsub : J ⊆ s := density_maximizer_subset s W
    have hWj : W j ≤ Kstar := Finset.le_convexHull_biUnion W hj
    have hWj_sub : (W j).carrier ⊆ Kstar.carrier := hWj
    have hscale_Kstar : r ≤ Metric.ethickness.scale ℝ Kstar.carrier := by
      have h_scale_Wj : (r : ENNReal) ≤ Metric.ethickness.scale ℝ (W j).carrier :=
        hthick j (hJsub hj)
      have h_scale_lex : ∀ (k : Fin (finrank ℝ E)),
          (r : ENNReal) ≤ Metric.ethickness ℝ (Kstar.carrier) (k : ℕ) := by
        intro k
        have hk_val : (r : ENNReal) ≤ Metric.ethickness ℝ ((W j).carrier) (k : ℕ) :=
          ((Metric.ethickness.le_scale_iff ((W j).carrier) (δ := r)).mp h_scale_Wj) k
        have hmono' : Metric.ethickness ℝ ((W j).carrier) (k : ℕ) ≤
            Metric.ethickness ℝ (Kstar.carrier) (k : ℕ) :=
          Metric.ethickness_monotone hWj_sub (k : ℕ)
        exact hk_val.trans hmono'
      exact (Metric.ethickness.le_scale_iff (Kstar.carrier) (δ := r)).mpr h_scale_lex
    rcases hmain Kstar hKstar_carrier hscale_Kstar with ⟨Q, hQ, hKsub, hvol⟩
    refine ⟨Q, hQ, ?_⟩
    rw [h_max_eq]
    have hKsub_Q : Kstar ≤ Q.toConvexSpaceBody := by simpa [Kstar]
    have h_filter_sub : {i ∈ s | W i ≤ Kstar}
        ⊆ {i ∈ s | W i ≤ Q.toConvexSpaceBody} := by
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, hi.2.trans hKsub_Q⟩
    have hsum_le : ∑ i ∈ s with W i ≤ Kstar, volume (W i).carrier
        ≤ ∑ i ∈ s with W i ≤ Q.toConvexSpaceBody, volume (W i).carrier :=
      Finset.sum_le_sum_of_subset h_filter_sub
    have hsum_eq : ∑ i ∈ s with W i ≤ Q.toConvexSpaceBody, volume (W i).carrier
        = densityIn s W Q.toConvexSpaceBody * volume (Q.toConvexSpaceBody).carrier := by
      rw [sum_volume_eq_densityIn_mul_volume s W Q.toConvexSpaceBody]
    have hvolQ : volume (Q.toConvexSpaceBody).carrier
        ≤ (exists_volume_bounded_prism_discretization.C n : ENNReal) * volume Kstar.carrier := by
      simpa using hvol
    have hsum_bound : ∑ i ∈ s with W i ≤ Kstar, volume (W i).carrier
        ≤ ((exists_volume_bounded_prism_discretization.C n : ENNReal) *
          densityIn s W Q.toConvexSpaceBody) * volume Kstar.carrier := by
      calc
        ∑ i ∈ s with W i ≤ Kstar, volume (W i).carrier
            ≤ ∑ i ∈ s with W i ≤ Q.toConvexSpaceBody, volume (W i).carrier := hsum_le
        _ = densityIn s W Q.toConvexSpaceBody * volume (Q.toConvexSpaceBody).carrier := hsum_eq
        _ ≤ densityIn s W Q.toConvexSpaceBody *
            ((exists_volume_bounded_prism_discretization.C n : ENNReal) * volume Kstar.carrier) :=
          by
          gcongr
        _ = ((exists_volume_bounded_prism_discretization.C n : ENNReal) *
          densityIn s W Q.toConvexSpaceBody) * volume Kstar.carrier := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    rw [densityIn_le_iff s W Kstar ((exists_volume_bounded_prism_discretization.C n : ENNReal) *
      densityIn s W Q.toConvexSpaceBody)]
    exact hsum_bound

/-! ### The finite test family on a ball of radius `R`

`exists_finite_test_family_maxDensity` is stated for families of convex bodies inside the closed
unit ball. The general-radius statement below is obtained from it by rescaling with the homothety
of centre `0` and ratio `R⁻¹`, the unit-ball lemma being used as a black box. The five auxiliary
lemmas isolate the elementary bookkeeping steps of that rescaling.
-/

/-- For `0 < r ≤ 1` and `1 ≤ R`, the rescaled scale `r / R` is again positive and at most `1`. -/
lemma exists_finite_test_family_maxDensity_closedBall.div_pos_and_div_le_one
    {r R : NNReal} (hr : 0 < r) (hr1 : r ≤ 1) (hR : 1 ≤ R) :
    0 < r / R ∧ r / R ≤ 1 := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hR
  constructor
  · rw [← NNReal.coe_pos, NNReal.coe_div]
    exact div_pos (by exact_mod_cast hr) (by exact_mod_cast hRpos)
  · rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_one]
    exact div_le_one_of_le₀ (by exact_mod_cast (hr1.trans hR)) (by exact_mod_cast hRpos.le)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The homothety of centre `0` and ratio `R⁻¹` maps a subset of the closed ball of radius `R`
into the closed unit ball. -/
lemma exists_finite_test_family_maxDensity_closedBall.homothety_subset_closedBall_one
    {R : NNReal} (hR : 0 < R) {W : Set E} (hW : W ⊆ Metric.closedBall (0 : E) (R : ℝ)) :
    AffineMap.homothety (0 : E) (R : ℝ)⁻¹ '' W ⊆ Metric.closedBall (0 : E) 1 := by
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy_cb : y ∈ Metric.closedBall (0 : E) (R : ℝ) := hW hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy_cb
  calc
    ‖AffineMap.homothety (0 : E) (R : ℝ)⁻¹ y‖ = ‖(R : ℝ)⁻¹ • y‖ := by
      simp [AffineMap.homothety_apply]
    _ = ‖(R : ℝ)⁻¹‖ * ‖y‖ := by rw [norm_smul]
    _ = |(R : ℝ)⁻¹| * ‖y‖ := by rw [Real.norm_eq_abs]
    _ = (R : ℝ)⁻¹ * ‖y‖ := by
      rw [abs_of_nonneg (inv_nonneg.mpr (by exact_mod_cast hR.le))]
    _ ≤ (R : ℝ)⁻¹ * (R : ℝ) := by
      have hpos : 0 ≤ (R : ℝ)⁻¹ := inv_nonneg.mpr (by exact_mod_cast hR.le)
      exact mul_le_mul_of_nonneg_left hy_cb hpos
    _ = 1 := by
      field_simp [show (R : ℝ) ≠ 0 from by exact_mod_cast hR.ne']

omit [MeasurableSpace E] [BorelSpace E] in
/-- By homogeneity of `Metric.ethickness.scale`, the homothety of centre `0` and ratio `R⁻¹`
turns the bound `r ≤ scale W` into `r / R ≤ scale` of the image. -/
lemma exists_finite_test_family_maxDensity_closedBall.le_scale_homothety_inv
    {r R : NNReal} (hR : 0 < R) {W : Set E}
    (hW : (r : ENNReal) ≤ Metric.ethickness.scale ℝ W) :
    ((r / R : NNReal) : ENNReal) ≤
      Metric.ethickness.scale ℝ (AffineMap.homothety (0 : E) (R : ℝ)⁻¹ '' W) := by
  have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne.symm
  have h_inv_ne_zero : (R : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero hRne
  have h_scale_eq : Metric.ethickness.scale ℝ (AffineMap.homothety (0 : E) (R : ℝ)⁻¹ '' W) =
      ‖(R : ℝ)⁻¹‖₊ * Metric.ethickness.scale ℝ W :=
    Metric.ethickness.scale_homothety_image (0 : E) h_inv_ne_zero W
  rw [h_scale_eq]
  calc
    ((r / R : NNReal) : ENNReal) = ((r : ENNReal) / (R : ENNReal)) := by
      rw [ENNReal.coe_div hR.ne.symm]
    _ = ((R : ENNReal)⁻¹ * (r : ENNReal)) := by rw [ENNReal.div_eq_inv_mul]
    _ = (‖(R : ℝ)⁻¹‖₊ : ENNReal) * (r : ENNReal) := by
      have h_nnnorm_inv : (‖(R : ℝ)⁻¹‖₊ : ENNReal) = (R : ENNReal)⁻¹ := by
        have hR_nonneg : 0 ≤ (R : ℝ) := by exact_mod_cast hR.le
        calc
          (‖(R : ℝ)⁻¹‖₊ : ENNReal) = ((‖(R : ℝ)⁻¹‖₊ : NNReal) : ENNReal) := rfl
          _ = ((R⁻¹ : NNReal) : ENNReal) := by
            have h_nn : ‖(R : ℝ)⁻¹‖₊ = (R⁻¹ : NNReal) := by
              calc
                ‖(R : ℝ)⁻¹‖₊ = ‖(R : ℝ)‖₊⁻¹ := by simp
                _ = (R : NNReal)⁻¹ := by
                  simp [Real.nnnorm_of_nonneg hR_nonneg]
                _ = (R⁻¹ : NNReal) := rfl
            simp [h_nn]
          _ = (R : ENNReal)⁻¹ := by rw [ENNReal.coe_inv hR.ne.symm]
      rw [h_nnnorm_inv]
    _ ≤ (‖(R : ℝ)⁻¹‖₊ : ENNReal) * Metric.ethickness.scale ℝ W := by
      gcongr

omit [Nontrivial E] in
/-- **Density transport along a prism homothety.**

Pulling the family of convex bodies back along the homothety of centre `x` and ratio `t⁻¹` is
the same, as far as `Kakeya.densityIn` is concerned, as pushing the test prism forward along the
homothety of centre `x` and ratio `t`. -/
lemma densityIn_prismHomothety {ι : Type*} {n : ℕ} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (P : PrismNDim n E E) (x : E) {t : NNReal} (ht : 0 < t) :
    densityIn s (fun i => (W i).homothety x (t : ℝ)⁻¹) P.toConvexSpaceBody
      = densityIn s W (P.homothety x t).toConvexSpaceBody := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne.symm
  have hinv0 : (t : ℝ)⁻¹ ≠ 0 := inv_ne_zero ht0
  have hbody :
      ((P.homothety x t).toConvexSpaceBody).homothety x (t : ℝ)⁻¹ = P.toConvexSpaceBody := by
    refine ConvexSpaceBody.ext ?_
    calc
      (((P.homothety x t).toConvexSpaceBody).homothety x (t : ℝ)⁻¹ : Set E)
          = AffineMap.homothety x (t : ℝ)⁻¹ '' ((P.homothety x t).toConvexSpaceBody).carrier := by
        rw [ConvexSpaceBody.coe_homothety]
      _ = AffineMap.homothety x (t : ℝ)⁻¹ '' ((P.homothety x t).carrier : Set E) := rfl
      _ = AffineMap.homothety x (t : ℝ)⁻¹ '' (AffineMap.homothety x (t : ℝ) '' P.carrier) := by
        rw [PrismNDim.carrier_homothety P x ht]
      _ = P.carrier := by rw [homothety_inv_image_homothety_image x ht0 P.carrier]
      _ = (P.toConvexSpaceBody : Set E) := rfl
  calc
    densityIn s (fun i => (W i).homothety x (t : ℝ)⁻¹) P.toConvexSpaceBody
        = densityIn s (fun i => (W i).homothety x (t : ℝ)⁻¹)
            (((P.homothety x t).toConvexSpaceBody).homothety x (t : ℝ)⁻¹) := by rw [hbody]
    _ = densityIn s W (P.homothety x t).toConvexSpaceBody := by
      rw [densityIn_homothety s W (P.homothety x t).toConvexSpaceBody x hinv0]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A cardinality bound at the rescaled scale `r / R` transfers to the image of the family under
the prism homothety of centre `0` and ratio `R`. -/
lemma exists_finite_test_family_maxDensity_closedBall.card_image_homothety_le
    [DecidableEq (PrismNDim (finrank ℝ E) E E)]
    {r R : NNReal} (_hr : 0 < r) (_hR : 0 < R)
    (QTest : Finset (PrismNDim (finrank ℝ E) E E))
    (hcard : (QTest.card : NNReal) ≤
      exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
        (r / R) ^ (-exists_volume_bounded_prism_discretization.M (finrank ℝ E))) :
    ((QTest.image fun P => P.homothety (0 : E) R).card : NNReal) ≤
      exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
        R ^ exists_volume_bounded_prism_discretization.M (finrank ℝ E) *
        r ^ (-exists_volume_bounded_prism_discretization.M (finrank ℝ E)) := by
  set C := exists_volume_bounded_prism_discretization.C (finrank ℝ E)
  set M := exists_volume_bounded_prism_discretization.M (finrank ℝ E)
  have hcard_image : (QTest.image fun P => P.homothety (0 : E) R).card ≤ QTest.card :=
    Finset.card_image_le
  have hcard_image_nnreal : ((QTest.image fun P => P.homothety (0 : E) R).card : NNReal) ≤
      (QTest.card : NNReal) := by exact_mod_cast hcard_image
  have hbound : ((QTest.image fun P => P.homothety (0 : E) R).card : NNReal) ≤ C * (r / R) ^ (-M) :=
    le_trans hcard_image_nnreal hcard
  have hcalc : (r / R : NNReal) ^ (-M) = R ^ M * r ^ (-M) := by
    calc
      (r / R : NNReal) ^ (-M) = ((r / R : NNReal) ^ M)⁻¹ := by rw [NNReal.rpow_neg]
      _ = (r ^ M / R ^ M)⁻¹ := by rw [NNReal.div_rpow]
      _ = (R ^ M / r ^ M) := by rw [inv_div]
      _ = R ^ M * (r ^ M)⁻¹ := by rw [div_eq_mul_inv]
      _ = R ^ M * r ^ (-M) := by rw [NNReal.rpow_neg]
  calc
    ((QTest.image fun P => P.homothety (0 : E) R).card : NNReal) ≤ C * (r / R) ^ (-M) := hbound
    _ = C * (R ^ M * r ^ (-M)) := by rw [hcalc]
    _ = C * R ^ M * r ^ (-M) := by ring

/-- **Finite prism test family for the maximal density on a ball of radius `R`.**

At every scale `0 < r ≤ 1` and every radius `R ≥ 1` there is a finite family of rectangular
prisms, of cardinality at most `C * R ^ M * r ^ (-M)` and depending only on `r`, `R` and the
dimension, that recovers the maximal density of any finite family of convex bodies (each
contained in the closed ball of radius `R` and with smallest affine thickness at least `r`) up to
the dimensional constant `C`.

This is the general-radius form of `exists_finite_test_family_maxDensity`, obtained from it by
the homothety of centre `0` and ratio `R⁻¹`. -/
theorem exists_finite_test_family_maxDensity_closedBall {r R : NNReal} (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : 1 ≤ R) :
    ∃ QTest : Finset (PrismNDim (finrank ℝ E) E E),
      (QTest.card : NNReal) ≤
          exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
            R ^ exists_volume_bounded_prism_discretization.M (finrank ℝ E) *
            r ^ (- exists_volume_bounded_prism_discretization.M (finrank ℝ E)) ∧
      ∀ {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E),
        (∀ i ∈ s, (W i).carrier ⊆ Metric.closedBall (0 : E) (R : ℝ)) →
        (∀ i ∈ s, r ≤ Metric.ethickness.scale ℝ (W i).carrier) →
        ∃ Q ∈ QTest, maxDensity s W ≤
          (exists_volume_bounded_prism_discretization.C (finrank ℝ E) : ENNReal) *
            densityIn s W Q.toConvexSpaceBody := by
  classical
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hinv : (R : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hRpos.ne')
  obtain ⟨hρpos, hρle⟩ :=
    exists_finite_test_family_maxDensity_closedBall.div_pos_and_div_le_one hr hr1 hR
  obtain ⟨QTest, hcard, hmain⟩ := exists_finite_test_family_maxDensity (E := E) hρpos hρle
  refine ⟨QTest.image fun P => P.homothety (0 : E) R, ?_, ?_⟩
  · exact exists_finite_test_family_maxDensity_closedBall.card_image_homothety_le hr hRpos
      QTest hcard
  intro ι s W hball hthick
  obtain ⟨Q', hQ', hle⟩ := hmain s (fun i => (W i).homothety (0 : E) (R : ℝ)⁻¹)
    (fun i hi => exists_finite_test_family_maxDensity_closedBall.homothety_subset_closedBall_one
      hRpos (hball i hi))
    (fun i hi => exists_finite_test_family_maxDensity_closedBall.le_scale_homothety_inv hRpos
      (hthick i hi))
  refine ⟨Q'.homothety (0 : E) R, Finset.mem_image_of_mem _ hQ', ?_⟩
  rwa [maxDensity_homothety s W (0 : E) hinv,
    densityIn_prismHomothety (E := E) s W Q' (0 : E) hRpos] at hle

/-- **Localized finite test family for the maximal density on a ball of radius `R`.**

Same content as `exists_finite_test_family_maxDensity_closedBall`, but the test bodies are
themselves *contained* in `Metric.closedBall 0 R`. It is obtained by intersecting every test
prism with that ball, which is free of charge: the input family already lies in the ball, so the
truncation changes neither which bodies are counted (the numerator of `Kakeya.densityIn`) nor,
except downwards, the volume of the test body (its denominator); hence the density can only go up.

The truncated members are no longer prisms, so this is stated separately rather than strengthening
`exists_finite_test_family_maxDensity_closedBall` in place. The index universe is the explicit
parameter `v` because `ι` is quantified *inside* the existential, so an auto-bound universe could
not be solved where a caller destructs the `∃`; callers pin it, e.g.
`exists_localized_finite_test_family_maxDensity.{u, _}`. -/
theorem exists_localized_finite_test_family_maxDensity {r R : NNReal} (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : 1 ≤ R) :
    ∃ KTest : Finset (ConvexSpaceBody E),
      (∀ K ∈ KTest, K.carrier ⊆ Metric.closedBall (0 : E) (R : ℝ)) ∧
      ((KTest.card : NNReal) ≤
        exists_volume_bounded_prism_discretization.C (finrank ℝ E) *
          R ^ exists_volume_bounded_prism_discretization.M (finrank ℝ E) *
          r ^ (- exists_volume_bounded_prism_discretization.M (finrank ℝ E))) ∧
      ∀ {ι : Type v} (s : Finset ι) (W : ι → ConvexSpaceBody E),
        (∀ i ∈ s, (W i).carrier ⊆ Metric.closedBall (0 : E) (R : ℝ)) →
        (∀ i ∈ s, (r : ENNReal) ≤ Metric.ethickness.scale ℝ (W i).carrier) →
        ∃ K ∈ KTest, maxDensity s W ≤
          (exists_volume_bounded_prism_discretization.C (finrank ℝ E) : ENNReal) *
            densityIn s W K := by
  classical
  obtain ⟨QTest, hcard, hmain⟩ :=
    exists_finite_test_family_maxDensity_closedBall.{_, v} (E := E) hr hr1 hR
  set B : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg with hB_def
  set f : PrismNDim (finrank ℝ E) E E → ConvexSpaceBody E := fun Q =>
    if h : (Q.toConvexSpaceBody.carrier ∩ B.carrier).Nonempty then
      Q.toConvexSpaceBody.inter B h else B with hf_def
  have hB_carrier : B.carrier = Metric.closedBall (0 : E) (R : ℝ) := rfl
  have hf_subset : ∀ Q : PrismNDim (finrank ℝ E) E E,
      (f Q).carrier ⊆ Metric.closedBall (0 : E) (R : ℝ) := by
    intro Q
    have hsub : (f Q).carrier ⊆ B.carrier := by
      simp only [hf_def]
      split_ifs with h
      · exact Set.inter_subset_right
      · exact subset_rfl
    exact hB_carrier ▸ hsub
  refine ⟨QTest.image f, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hK
    exact hf_subset Q
  · refine le_trans ?_ hcard
    exact_mod_cast Finset.card_image_le
  · intro ι s W hball hthick
    obtain ⟨Q, hQ, hle⟩ := hmain s W hball hthick
    refine ⟨f Q, Finset.mem_image_of_mem f hQ, hle.trans ?_⟩
    gcongr
    by_cases h : (Q.toConvexSpaceBody.carrier ∩ B.carrier).Nonempty
    · -- The truncation keeps the numerator and shrinks the denominator.
      have hfQ : f Q = Q.toConvexSpaceBody.inter B h := by simp only [hf_def, dif_pos h]
      have hfilter : {i ∈ s | W i ≤ Q.toConvexSpaceBody} = {i ∈ s | W i ≤ f Q} := by
        refine Finset.filter_congr fun i hi => ?_
        rw [hfQ]
        exact ⟨fun hiQ x hx => ⟨hiQ hx, hball i hi hx⟩, fun hiQ x hx => (hiQ hx).1⟩
      have hvol : volume (f Q).carrier ≤ volume Q.toConvexSpaceBody.carrier := by
        rw [hfQ]
        exact measure_mono Set.inter_subset_left
      simp only [densityIn]
      rw [hfilter]
      gcongr
    · -- No member of the family fits inside `Q`, so the density on `Q` already vanishes.
      have hfilter_empty : {i ∈ s | W i ≤ Q.toConvexSpaceBody} = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun {i} hi hiQ => ?_
        obtain ⟨x, hx⟩ := (W i).nonempty'
        exact h ⟨x, hiQ hx, hball i hi hx⟩
      simp only [densityIn, hfilter_empty, Finset.sum_empty, ENNReal.zero_div, zero_le]

end Kakeya
