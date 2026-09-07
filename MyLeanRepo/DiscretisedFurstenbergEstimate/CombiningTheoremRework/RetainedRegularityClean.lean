module

/-
  Retained Square-Root Regularity (SELF-CONTAINED)

  Composes loss factors when restricting a square-root regular set
  to a B1-retained subset:
    1. Geometric packing loss (factor 9)
    2. B1 global retention loss (K_global)

  Main results:
  - `thin_preserves_sset_by_density_clean` — density-aware S-set restriction
  - `finset_squares_ncover_lower_clean` — factor-9 packing lower bound
  - `subset_regular_with_density` — general regularity-with-density lemma
  - `global_retained_regular_clean` — B1-retained GLOBAL point set
  - `step5_retained_regularity_corrected` — Step 5 with corrected exponents

  NO contaminated imports. All geometric facts reproved inline.
  Imports: Base, RegularIncidence.Definitions, CombiningTheorem, Mathlib.

  Whiteprint node: CombiningTheoremRework / retained_regularity
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Plane
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-! ========================================================================
   Self-contained geometric lemmas
   ======================================================================== -/

/-- Center of a dyadic square. -/
def retainedSquareCenter {n : ℕ} (δ : ℝ) (Q : DyadicSquare n) : Plane :=
  WithLp.toLp 2 ![((Q.i : ℝ) + 1 / 2) * δ, ((Q.j : ℝ) + 1 / 2) * δ]

/-- A dyadic square of side δ is contained in the closed ball of radius δ
    around its center. -/
lemma retainedSquare_covered_by_center {n : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta n) (Q : DyadicSquare n) :
    (Q.toSet : Set Plane) ⊆ Metric.closedBall (retainedSquareCenter δ Q) δ := by
  let c := retainedSquareCenter δ Q
  intro x hx
  have hxi1 : (Q.i : ℝ) * dyadicDelta n ≤ x 0 := hx.1
  have hxi2 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta n := hx.2.1
  have hxj1 : (Q.j : ℝ) * dyadicDelta n ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta n := hx.2.2.2
  have h1 : |x 0 - c 0| ≤ δ / 2 := by
    have h4 : c 0 = ((Q.i : ℝ) + 1 / 2) * δ := by simp [c, retainedSquareCenter] <;> rfl
    have h7 : (Q.i : ℝ) * δ ≤ x 0 := by rw [show (Q.i : ℝ) * dyadicDelta n = (Q.i : ℝ) * δ from by rw [hδ_eq]] at hxi1; exact hxi1
    have h9 : x 0 < ((Q.i : ℝ) + 1) * δ := by rw [show ((Q.i : ℝ) + 1) * dyadicDelta n = ((Q.i : ℝ) + 1) * δ from by rw [hδ_eq]] at hxi2; exact hxi2
    rw [h4, abs_sub_le_iff] <;> constructor <;> linarith
  have h2 : |x 1 - c 1| ≤ δ / 2 := by
    have h4 : c 1 = ((Q.j : ℝ) + 1 / 2) * δ := by simp [c, retainedSquareCenter] <;> rfl
    have h7 : (Q.j : ℝ) * δ ≤ x 1 := by rw [show (Q.j : ℝ) * dyadicDelta n = (Q.j : ℝ) * δ from by rw [hδ_eq]] at hxj1; exact hxj1
    have h9 : x 1 < ((Q.j : ℝ) + 1) * δ := by rw [show ((Q.j : ℝ) + 1) * dyadicDelta n = ((Q.j : ℝ) + 1) * δ from by rw [hδ_eq]] at hxj2; exact hxj2
    rw [h4, abs_sub_le_iff] <;> constructor <;> linarith
  have h3 : dist x c ≤ δ := by
    have h4 : dist x c ^ 2 = (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq x c] <;> simp [Fin.sum_univ_two, Real.dist_eq] <;> ring
    have h6 : (x 0 - c 0) ^ 2 ≤ (δ / 2) ^ 2 := by nlinarith [abs_le.mp h1]
    have h8 : (x 1 - c 1) ^ 2 ≤ (δ / 2) ^ 2 := by nlinarith [abs_le.mp h2]
    have h10 : dist x c ^ 2 ≤ δ ^ 2 := by rw [h4] <;> nlinarith
    have h12 : 0 ≤ dist x c := by positivity
    nlinarith
  exact h3

/-- A Euclidean ball of radius δ intersects at most 9 dyadic squares of side δ. -/
lemma retainedBall_intersects_at_most_9_squares {n : ℕ} (c : Plane) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta n) :
    ∃ (I : Finset (DyadicSquare n)), I.card ≤ 9 ∧
      ∀ (q : DyadicSquare n), (q.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ → q ∈ I := by
  let i0 : ℤ := ⌊c 0 / δ⌋
  let j0 : ℤ := ⌊c 1 / δ⌋
  let indices_i : Finset ℤ := Finset.Icc (i0 - 1) (i0 + 1)
  let indices_j : Finset ℤ := Finset.Icc (j0 - 1) (j0 + 1)
  classical
  let I : Finset (DyadicSquare n) :=
    indices_i.biUnion fun i => indices_j.image (fun j => ⟨i, j⟩)
  have hI_card : I.card ≤ 9 := by
    have h_card3 : ∀ (z : ℤ), (Finset.Icc (z - 1) (z + 1)).card = 3 := by
      intro z; simp [Finset.Icc_eq_empty_of_lt] <;> omega
    have h_inj : ∀ (i : ℤ), Function.Injective (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n)) := by
      intro i _ _ h; simpa [DyadicSquare.mk.injEq] using h
    calc I.card
      ≤ ∑ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card := Finset.card_biUnion_le
    _ = ∑ i ∈ indices_i, indices_j.card := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.card_image_of_injective _ (h_inj i)]
    _ = indices_i.card * indices_j.card := by rw [Finset.sum_const] <;> ring
    _ = 3 * 3 := by rw [h_card3 i0, h_card3 j0] <;> norm_num
    _ = 9 := by norm_num
  refine ⟨I, hI_card, ?_⟩
  intro q hq
  have h_nonempty : ((q.toSet : Set Plane) ∩ Metric.closedBall c δ).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hq
  rcases h_nonempty with ⟨p, hpQ, hpc⟩
  have hqi1 : (q.i : ℝ) * δ ≤ p 0 := by have h := hpQ.1; rw [hδ_eq.symm] at h; exact h
  have hqi2 : p 0 < ((q.i : ℝ) + 1) * δ := by have h := hpQ.2.1; rw [hδ_eq.symm] at h; exact h
  have hqj1 : (q.j : ℝ) * δ ≤ p 1 := by have h := hpQ.2.2.1; rw [hδ_eq.symm] at h; exact h
  have hqj2 : p 1 < ((q.j : ℝ) + 1) * δ := by have h := hpQ.2.2.2; rw [hδ_eq.symm] at h; exact h
  have hpi_coord : |p 0 - c 0| ≤ δ := by
    have hdist2 : dist p c ^ 2 = (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 := by
      have h : dist p c ^ 2 = ∑ i : Fin 2, dist (p i) (c i) ^ 2 := EuclideanSpace.dist_sq_eq p c
      rw [h]
      have h2 : ∑ i : Fin 2, dist (p i) (c i) ^ 2 = dist (p 0) (c 0) ^ 2 + dist (p 1) (c 1) ^ 2 := by
        simp [Fin.sum_univ_two] <;> ring
      rw [h2]
      have h3 : ∀ (a b : ℝ), dist a b ^ 2 = (a - b) ^ 2 := by intro a b; simp [Real.dist_eq] <;> ring
      rw [h3 (p 0) (c 0), h3 (p 1) (c 1)] <;> ring
    have hnonneg : 0 ≤ (p 1 - c 1) ^ 2 := by positivity
    have hsq : (p 0 - c 0) ^ 2 ≤ dist p c ^ 2 := by
      rw [hdist2] <;> linarith
    have habs : |p 0 - c 0| ≤ dist p c := by
      have h4 : |p 0 - c 0| ^ 2 ≤ (dist p c) ^ 2 := by
        have h5 : |p 0 - c 0| ^ 2 = (p 0 - c 0) ^ 2 := by simp [sq_abs]
        rw [h5]; exact hsq
      have h6 : 0 ≤ dist p c := by positivity
      nlinarith [abs_nonneg (p 0 - c 0)]
    exact habs.trans hpc
  have hpj_coord : |p 1 - c 1| ≤ δ := by
    have hdist2 : dist p c ^ 2 = (p 0 - c 0) ^ 2 + (p 1 - c 1) ^ 2 := by
      have h : dist p c ^ 2 = ∑ i : Fin 2, dist (p i) (c i) ^ 2 := EuclideanSpace.dist_sq_eq p c
      rw [h]
      have h2 : ∑ i : Fin 2, dist (p i) (c i) ^ 2 = dist (p 0) (c 0) ^ 2 + dist (p 1) (c 1) ^ 2 := by
        simp [Fin.sum_univ_two] <;> ring
      rw [h2]
      have h3 : ∀ (a b : ℝ), dist a b ^ 2 = (a - b) ^ 2 := by intro a b; simp [Real.dist_eq] <;> ring
      rw [h3 (p 0) (c 0), h3 (p 1) (c 1)] <;> ring
    have hnonneg : 0 ≤ (p 0 - c 0) ^ 2 := by positivity
    have hsq : (p 1 - c 1) ^ 2 ≤ dist p c ^ 2 := by
      rw [hdist2] <;> linarith
    have habs : |p 1 - c 1| ≤ dist p c := by
      have h4 : |p 1 - c 1| ^ 2 ≤ (dist p c) ^ 2 := by
        have h5 : |p 1 - c 1| ^ 2 = (p 1 - c 1) ^ 2 := by simp [sq_abs]
        rw [h5]; exact hsq
      have h6 : 0 ≤ dist p c := by positivity
      nlinarith [abs_nonneg (p 1 - c 1)]
    exact habs.trans hpc
  have h_floor1 : (i0 : ℝ) ≤ c 0 / δ := Int.floor_le (c 0 / δ)
  have h_floor2 : c 0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one (c 0 / δ)
  have h_i_lower : i0 - 1 ≤ q.i := by
    have h1 : p 0 ≥ c 0 - δ := by rw [abs_sub_le_iff] at hpi_coord <;> linarith
    have h2 : ((q.i : ℝ) + 1) * δ > c 0 - δ := by linarith [hqi2]
    have h3 : (q.i : ℝ) > c 0 / δ - 2 := by
      have h4 : ((q.i : ℝ) + 1) * δ / δ > (c 0 - δ) / δ := by gcongr
      have h5 : ((q.i : ℝ) + 1) * δ / δ = (q.i : ℝ) + 1 := by field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 0 - δ) / δ = c 0 / δ - 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4; linarith
    have h7 : (q.i : ℝ) > (i0 : ℝ) - 2 := by linarith [h_floor1]
    by_contra h10; have h11 : q.i ≤ i0 - 2 := by linarith
    have h12 : (q.i : ℝ) ≤ (i0 : ℝ) - 2 := by exact_mod_cast h11
    linarith
  have h_i_upper : q.i ≤ i0 + 1 := by
    have h1 : p 0 ≤ c 0 + δ := by rw [abs_sub_le_iff] at hpi_coord <;> linarith
    have h2 : (q.i : ℝ) * δ ≤ c 0 + δ := by linarith [hqi1]
    have h3 : (q.i : ℝ) ≤ c 0 / δ + 1 := by
      have h4 : (q.i : ℝ) * δ / δ ≤ (c 0 + δ) / δ := by gcongr
      have h5 : (q.i : ℝ) * δ / δ = (q.i : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 0 + δ) / δ = c 0 / δ + 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4; exact h4
    have h7 : (q.i : ℝ) < (i0 : ℝ) + 2 := by linarith [h_floor2]
    by_contra h9; have h10 : q.i ≥ i0 + 2 := by linarith
    have h11 : (q.i : ℝ) ≥ (i0 : ℝ) + 2 := by exact_mod_cast h10
    linarith
  have h_j_lower : j0 - 1 ≤ q.j := by
    have h1 : p 1 ≥ c 1 - δ := by rw [abs_sub_le_iff] at hpj_coord <;> linarith
    have h2 : ((q.j : ℝ) + 1) * δ > c 1 - δ := by linarith [hqj2]
    have h3 : (q.j : ℝ) > c 1 / δ - 2 := by
      have h4 : ((q.j : ℝ) + 1) * δ / δ > (c 1 - δ) / δ := by gcongr
      have h5 : ((q.j : ℝ) + 1) * δ / δ = (q.j : ℝ) + 1 := by field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 1 - δ) / δ = c 1 / δ - 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4; linarith
    have h7 : (q.j : ℝ) > (j0 : ℝ) - 2 := by linarith [Int.floor_le (c 1 / δ)]
    by_contra h10; have h11 : q.j ≤ j0 - 2 := by linarith
    have h12 : (q.j : ℝ) ≤ (j0 : ℝ) - 2 := by exact_mod_cast h11
    linarith
  have h_j_upper : q.j ≤ j0 + 1 := by
    have h1 : p 1 ≤ c 1 + δ := by rw [abs_sub_le_iff] at hpj_coord <;> linarith
    have h2 : (q.j : ℝ) * δ ≤ c 1 + δ := by linarith [hqj1]
    have h3 : (q.j : ℝ) ≤ c 1 / δ + 1 := by
      have h4 : (q.j : ℝ) * δ / δ ≤ (c 1 + δ) / δ := by gcongr
      have h5 : (q.j : ℝ) * δ / δ = (q.j : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
      have h6 : (c 1 + δ) / δ = c 1 / δ + 1 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h5, h6] at h4; exact h4
    have h7 : (q.j : ℝ) < (j0 : ℝ) + 2 := by linarith [Int.lt_floor_add_one (c 1 / δ)]
    by_contra h9; have h10 : q.j ≥ j0 + 2 := by linarith
    have h11 : (q.j : ℝ) ≥ (j0 : ℝ) + 2 := by exact_mod_cast h10
    linarith
  have hqi_in : q.i ∈ indices_i := by simp only [indices_i, Finset.mem_Icc] <;> omega
  have hqj_in : q.j ∈ indices_j := by simp only [indices_j, Finset.mem_Icc] <;> omega
  have hq_in_I : q ∈ I := by
    simp only [I, Finset.mem_biUnion]
    refine ⟨q.i, hqi_in, ?_⟩
    simpa [Finset.mem_image] using ⟨q.j, hqj_in, rfl⟩
  exact hq_in_I

/-! ========================================================================
   Self-contained: density-aware S-set preservation
   ======================================================================== -/

/-- Density-aware S-set preservation under subsets. -/
lemma thin_preserves_sset_by_density_clean
    {X : Type*} [PseudoMetricSpace X]
    {δ s C K : ℝ} {E E' : Set X}
    (hE : IsDeltaSSet δ s C E)
    (h_sub : E' ⊆ E)
    (hE'_nonempty : E'.Nonempty)
    (hK_pos : 0 < K)
    (h_density : (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) ≤
                 ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal E' : ENNReal)) :
    IsDeltaSSet δ s (C * K) E' := by
  rcases hE with ⟨_, hδ_pos, hC_pos, hs_nonneg, hcover⟩
  have hCK_pos : 0 < C * K := mul_pos hC_pos hK_pos
  have hCK : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
    rw [←ENNReal.ofReal_mul hC_pos.le] <;> rfl
  refine' ⟨hE'_nonempty, hδ_pos, hCK_pos, hs_nonneg, _⟩
  intro x r hr
  let N_E' := (Metric.externalCoveringNumber δ.toNNReal E' : ENNReal)
  let N_E := (Metric.externalCoveringNumber δ.toNNReal E : ENNReal)
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (E' ∩ Metric.closedBall x r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal (E ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (by gcongr)
  have h2 := hcover x r hr
  have h3 : N_E ≤ ENNReal.ofReal K * N_E' := h_density
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * N_E ≤
            ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') := by gcongr
  have h5 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') =
            (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s * N_E' := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  have h6 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * N_E') ≤
            ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s * N_E' := by
    rw [h5, hCK]
  exact le_trans (le_trans h1 h2) (le_trans h4 h6)

/-! ========================================================================
   Factor-9 packing lower bound for dyadic squares
   ======================================================================== -/

/-- Lower bound: |P_Q| ≤ 9 * Ncover(δ_n, union of squares in P_Q). -/
lemma finset_squares_ncover_lower_clean
    {n : ℕ} (P_Q : Finset (DyadicSquare n)) :
    (P_Q.card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set Plane)) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let E := (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set Plane))
  have h_main : ∀ (C : Set Plane), Metric.IsCover δ.toNNReal E C →
      (P_Q.card : ℕ∞) ≤ 9 * C.encard := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set Plane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : Plane) : Finset (DyadicSquare n) :=
        P_Q.filter (fun p => (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases retainedBall_intersects_at_most_9_squares c δ hδ_pos rfl with ⟨I, hI9, hI_mem⟩
        have h4 : Q_c c ⊆ I := by
          intro p hp
          have h5 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := (Finset.mem_filter.mp hp).2
          exact hI_mem p h5
        have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
        have h6 : I.card ≤ 9 := hI9
        linarith
      have h4 : P_Q ⊆ Cfin.biUnion Q_c := by
        intro p hp
        have h10 : (p.toSet : Set Plane).Nonempty := DyadicSquare.toSet_nonempty p
        rcases h10 with ⟨x, hxp⟩
        have hxE : x ∈ E := Set.mem_iUnion₂.mpr ⟨p, hp, hxp⟩
        rcases hC hxE with ⟨c, hc, hball⟩
        have hc_in : c ∈ Cfin := by
          simpa [Cfin, h2] using hc
        have hball' : x ∈ Metric.closedBall c δ := by
          have h_nndist : nndist x c ≤ δ.toNNReal := by simpa [Set.mem_setOf_eq] using hball
          have h_dist : dist x c ≤ δ := by
            have h1 : (nndist x c : ℝ) ≤ (δ.toNNReal : ℝ) := by exact_mod_cast h_nndist
            have h2 : (nndist x c : ℝ) = dist x c := by simp
            have h3 : (δ.toNNReal : ℝ) = δ := by simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
            rw [h2, h3] at h1
            exact h1
          have h4 : dist x c ≤ δ := h_dist
          simpa [Metric.mem_closedBall] using h4
        have h6 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have hne : ((p.toSet : Set Plane) ∩ Metric.closedBall c δ).Nonempty := ⟨x, hxp, hball'⟩
          exact Set.nonempty_iff_ne_empty.mp hne
        have h7 : p ∈ Q_c c := by simp only [Q_c, Finset.mem_filter] <;> exact ⟨hp, h6⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc_in, h7⟩
      have h5 : P_Q.card ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
      have h5' : P_Q.card ≤ ∑ c ∈ Cfin, (Q_c c).card :=
        le_trans h5 (Finset.card_biUnion_le)
      have h6 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
        apply Finset.sum_le_sum; intro c hc; exact h3 c hc
      have h7 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by simp [Finset.sum_const] <;> ring
      have h8 : P_Q.card ≤ 9 * Cfin.card := by
        calc P_Q.card
            ≤ ∑ c ∈ Cfin, (Q_c c).card := h5'
          _ ≤ ∑ c ∈ Cfin, (9 : ℕ) := h6
          _ = 9 * Cfin.card := h7
      have h9 : C.encard = ↑Cfin.card := by
        have h10 : (Cfin : Set Plane) = C := h2
        have h11 : C.encard = (Cfin : Set Plane).encard := by rw [h10]
        have h12 : (Cfin : Set Plane).encard = ↑Cfin.card := by simp
        exact Eq.trans h11 h12
      rw [h9]
      exact_mod_cast h8
    · have hinf : C.encard = ⊤ := by
        have h : Set.Infinite C := hCfin
        exact Set.encard_eq_top_iff.mpr h
      rw [hinf]
      <;> simp
  have h_iInf : (P_Q.card : ℕ∞) ≤
      ⨅ (C : Set Plane) (_ : Metric.IsCover δ.toNNReal E C), 9 * C.encard :=
    le_iInf fun C => le_iInf fun hC => h_main C hC
  have h9ne : (9 : ℕ∞) ≠ 0 := by norm_num
  have h_mul1 : 9 * Metric.externalCoveringNumber δ.toNNReal E =
      ⨅ (C : Set Plane), 9 * (⨅ (hC : Metric.IsCover δ.toNNReal E C), C.encard) := by
    simp only [Metric.externalCoveringNumber]
    rw [ENat.mul_iInf_of_ne h9ne]
  have h_mul2 : ∀ (C : Set Plane),
      9 * (⨅ (hC : Metric.IsCover δ.toNNReal E C), C.encard) =
      ⨅ (hC : Metric.IsCover δ.toNNReal E C), 9 * C.encard := by
    intro C
    rw [ENat.mul_iInf_of_ne h9ne]
  have h_mul : 9 * Metric.externalCoveringNumber δ.toNNReal E =
      ⨅ (C : Set Plane), ⨅ (hC : Metric.IsCover δ.toNNReal E C), 9 * C.encard := by
    rw [h_mul1]
    apply congr_arg
    funext C
    exact h_mul2 C
  have h_final : (P_Q.card : ℕ∞) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal E := by
    have h_eq : (⨅ (C : Set Plane), ⨅ (hC : Metric.IsCover δ.toNNReal E C), 9 * C.encard) =
        9 * Metric.externalCoveringNumber δ.toNNReal E := h_mul.symm
    exact le_trans h_iInf (le_of_eq h_eq)
  exact_mod_cast h_final

/-! ========================================================================
   Helper: Bound on squares intersecting a point set
   ======================================================================== -/

/-- If every square in `S` intersects `pointSet`, then `|S| ≤ 9 * Ncover(δ_n, pointSet)`.
    Clean version with no contaminated imports. -/
lemma finset_intersecting_squares_bound_clean
    {n : ℕ} {S : Finset (DyadicSquare n)} {pointSet : Set Plane}
    (h : ∀ Q ∈ S, ((Q.toSet : Set Plane) ∩ pointSet).Nonempty) :
    (S.card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal pointSet := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_main : ∀ (C : Set Plane), Metric.IsCover δ.toNNReal pointSet C →
      (S.card : ℕ∞) ≤ 9 * C.encard := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set Plane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : Plane) : Finset (DyadicSquare n) :=
        S.filter (fun p => (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases retainedBall_intersects_at_most_9_squares c δ hδ_pos rfl with ⟨I, hI9, hI_mem⟩
        have h4 : Q_c c ⊆ I := by
          intro p hp
          have h5 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := (Finset.mem_filter.mp hp).2
          exact hI_mem p h5
        have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
        have h6 : I.card ≤ 9 := hI9
        linarith
      have h4 : S ⊆ Cfin.biUnion Q_c := by
        intro p hp
        rcases h p hp with ⟨x, hxp, hxP⟩
        rcases hC hxP with ⟨c, hc, hball⟩
        have hc_in : c ∈ Cfin := by simpa [Cfin, h2] using hc
        have hball' : x ∈ Metric.closedBall c δ := by
          have h_nndist : nndist x c ≤ δ.toNNReal := by simpa [Set.mem_setOf_eq] using hball
          have h_dist : dist x c ≤ δ := by
            have h1 : (nndist x c : ℝ) ≤ (δ.toNNReal : ℝ) := by exact_mod_cast h_nndist
            have h2 : (nndist x c : ℝ) = dist x c := by simp
            have h3 : (δ.toNNReal : ℝ) = δ := by simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
            rw [h2, h3] at h1; exact h1
          simpa [Metric.mem_closedBall] using h_dist
        have h6 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have hne : ((p.toSet : Set Plane) ∩ Metric.closedBall c δ).Nonempty := ⟨x, hxp, hball'⟩
          exact Set.nonempty_iff_ne_empty.mp hne
        have h7 : p ∈ Q_c c := by simp only [Q_c, Finset.mem_filter] <;> exact ⟨hp, h6⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc_in, h7⟩
      have h5 : S.card ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
      have h5' : S.card ≤ ∑ c ∈ Cfin, (Q_c c).card := le_trans h5 (Finset.card_biUnion_le)
      have h6 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
        apply Finset.sum_le_sum; intro c hc; exact h3 c hc
      have h7 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by simp [Finset.sum_const] <;> ring
      have h8 : S.card ≤ 9 * Cfin.card := by
        calc S.card
            ≤ ∑ c ∈ Cfin, (Q_c c).card := h5'
          _ ≤ ∑ c ∈ Cfin, (9 : ℕ) := h6
          _ = 9 * Cfin.card := h7
      have h9 : C.encard = ↑Cfin.card := by
        have h10 : (Cfin : Set Plane) = C := h2
        have h11 : C.encard = (Cfin : Set Plane).encard := by rw [h10]
        have h12 : (Cfin : Set Plane).encard = ↑Cfin.card := by simp
        exact Eq.trans h11 h12
      rw [h9]
      exact_mod_cast h8
    · have hinf : C.encard = ⊤ := by
        have h : Set.Infinite C := hCfin
        exact Set.encard_eq_top_iff.mpr h
      rw [hinf] <;> simp
  have h_iInf : (S.card : ℕ∞) ≤
      ⨅ (C : Set Plane) (_ : Metric.IsCover δ.toNNReal pointSet C), 9 * C.encard :=
    le_iInf fun C => le_iInf fun hC => h_main C hC
  have h9ne : (9 : ℕ∞) ≠ 0 := by norm_num
  have h_mul1 : 9 * Metric.externalCoveringNumber δ.toNNReal pointSet =
      ⨅ (C : Set Plane), 9 * (⨅ (hC : Metric.IsCover δ.toNNReal pointSet C), C.encard) := by
    simp only [Metric.externalCoveringNumber]
    rw [ENat.mul_iInf_of_ne h9ne]
  have h_mul2 : ∀ (C : Set Plane),
      9 * (⨅ (hC : Metric.IsCover δ.toNNReal pointSet C), C.encard) =
      ⨅ (hC : Metric.IsCover δ.toNNReal pointSet C), 9 * C.encard := by
    intro C
    rw [ENat.mul_iInf_of_ne h9ne]
  have h_mul : 9 * Metric.externalCoveringNumber δ.toNNReal pointSet =
      ⨅ (C : Set Plane), ⨅ (hC : Metric.IsCover δ.toNNReal pointSet C), 9 * C.encard := by
    rw [h_mul1]
    apply congr_arg
    funext C
    exact h_mul2 C
  have h_final : (S.card : ℕ∞) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal pointSet := by
    have h_eq : (⨅ (C : Set Plane), ⨅ (hC : Metric.IsCover δ.toNNReal pointSet C), 9 * C.encard) =
        9 * Metric.externalCoveringNumber δ.toNNReal pointSet := h_mul.symm
    exact le_trans h_iInf (le_of_eq h_eq)
  exact_mod_cast h_final

/-! ========================================================================
   Helper: Upper bound Ncover(δ_n, pointSet) ≤ |P₀|
   ======================================================================== -/

/-- Upper bound: Ncover(δ_n, config.pointSet) ≤ |config.P₀| via center covering. -/
lemma retained_pointSet_ncover_upper_clean {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C₁ M) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet ≤
      (config.P₀.card : ENNReal) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let centers : Finset Plane := config.P₀.image (fun p : DyadicSquare n => retainedSquareCenter δ p)
  have h1 : config.pointSet ⊆ ⋃ c ∈ (centers : Set Plane), Metric.closedBall c δ.toNNReal := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨p, hp, hyp⟩
    let c := retainedSquareCenter δ p
    have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hcov : y ∈ Metric.closedBall c δ := retainedSquare_covered_by_center hδ_pos (by rfl) p hyp
    have hcov' : y ∈ Metric.closedBall c δ.toNNReal := by
      have h5 : ((δ.toNNReal : ℝ)) = δ := by simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
      simpa [Metric.mem_closedBall, h5] using hcov
    exact Set.mem_iUnion₂.mpr ⟨c, hc_in, hcov'⟩
  have h_iscover : Metric.IsCover δ.toNNReal config.pointSet (centers : Set _) :=
    Metric.IsCover.of_subset_iUnion_closedBall h1
  have h6 : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤ (centers : Set Plane).encard :=
    h_iscover.externalCoveringNumber_le_encard
  have h7 : (centers : Set Plane).encard = ↑centers.card := by simp
  have h8 : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤ ↑centers.card := by
    rw [h7] at h6; exact h6
  have h9 : centers.card ≤ config.P₀.card := Finset.card_image_le
  have h10 : (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤ (config.P₀.card : ENNReal) := by
    exact_mod_cast (le_trans h8 (by exact_mod_cast h9))
  exact h10

/-! ========================================================================
   General lemma: subset regularity with density
   ======================================================================== -/

/-- If E is square-root regular and E' ⊆ E with density
    Ncover(δ,E) ≤ K_density * Ncover(δ,E'), then E' is square-root regular
    with S-set constant C * K_density. Sqrt bound K preserved. -/
lemma subset_regular_with_density
    {δ t C K K_density : ℝ} {E E' : Set Plane}
    (hReg : IsSquareRootRegular δ t C K E)
    (h_sub : E' ⊆ E)
    (hE'_nonempty : E'.Nonempty)
    (hK_density_pos : 0 < K_density)
    (h_density : (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) ≤
        ENNReal.ofReal K_density * (Metric.externalCoveringNumber δ.toNNReal E' : ENNReal)) :
    IsSquareRootRegular δ t (C * K_density) K E' := by
  have h_sset : IsDeltaSSet δ t (C * K_density) E' :=
    thin_preserves_sset_by_density_clean hReg.1 h_sub hE'_nonempty hK_density_pos h_density
  have h_sqrt : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal E' : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow δ (-t / 2)) := by
    have h_mono : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal E' ≤
        Metric.externalCoveringNumber (Real.sqrt δ).toNNReal E :=
      Metric.externalCoveringNumber_mono_set h_sub
    have h_mono' : (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal E' : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.sqrt δ).toNNReal E : ENNReal) := by exact_mod_cast h_mono
    exact le_trans h_mono' hReg.2
  exact ⟨h_sset, h_sqrt⟩

/-! ========================================================================
   Global B1-retained point set regularity

   Loss: K_density = 9 * K_global
   Chain: Ncover(E) ≤ |P₀| ≤ K_global * |P| ≤ K_global * 9 * Ncover(E')
   ======================================================================== -/

/-- Global B1-retained point set is square-root regular.
    Result S-set constant: C * 9 * K_global. Sqrt-scale K preserved. -/
theorem global_retained_regular_clean
    {n : ℕ} {s t C K C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (hReg : IsSquareRootRegular (dyadicDelta n) t C K config.pointSet)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.P₀)
    (K_global : ℝ) (hK_global_pos : 0 < K_global)
    (h_global_ret : (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ))
    (hP_nonempty : P.Nonempty) :
    IsSquareRootRegular (dyadicDelta n) t (C * 9 * K_global) K
      (⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set Plane)) := by
  let δ_n := dyadicDelta n
  let E := config.pointSet
  let E' : Set Plane := ⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set Plane)
  let Ncover_E : ENNReal := Metric.externalCoveringNumber δ_n.toNNReal E
  let Ncover_E' : ENNReal := Metric.externalCoveringNumber δ_n.toNNReal E'
  have hδ_pos : 0 < δ_n := dyadicDelta_pos n

  have h_sub : E' ⊆ E := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_p_in_P0 : p ∈ config.P₀ := hP_sub hp
    exact Set.mem_iUnion₂.mpr ⟨p, h_p_in_P0, hxp⟩

  have hE'_nonempty : E'.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h_nonempty : (p.toSet : Set Plane).Nonempty := DyadicSquare.toSet_nonempty p
    rcases h_nonempty with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩⟩

  have h_upper : Ncover_E ≤ (config.P₀.card : ENNReal) := retained_pointSet_ncover_upper_clean config
  have h_lower : (P.card : ENNReal) ≤ (9 : ENNReal) * Ncover_E' := finset_squares_ncover_lower_clean P

  let K_density := 9 * K_global
  have hK_density_pos : 0 < K_density := by positivity
  have h_density : Ncover_E ≤ ENNReal.ofReal K_density * Ncover_E' := by
    calc Ncover_E
        ≤ (config.P₀.card : ENNReal) := h_upper
      _ ≤ ENNReal.ofReal (K_global * (P.card : ℝ)) := by
        have h_cast : (config.P₀.card : ENNReal) = ENNReal.ofReal (config.P₀.card : ℝ) := by simp
        rw [h_cast]; exact ENNReal.ofReal_le_ofReal h_global_ret
      _ = ENNReal.ofReal K_global * (P.card : ENNReal) := by
        have hKg_nonneg : 0 ≤ K_global := by linarith
        simp [ENNReal.ofReal_mul hKg_nonneg] <;> norm_cast
      _ ≤ ENNReal.ofReal K_global * ((9 : ENNReal) * Ncover_E') := by gcongr
      _ = ENNReal.ofReal K_density * Ncover_E' := by
        have hKg_nonneg : 0 ≤ K_global := by linarith
        have h_step1 : ENNReal.ofReal K_global * ((9 : ENNReal) * Ncover_E') =
            (ENNReal.ofReal K_global * (9 : ENNReal)) * Ncover_E' := by simp [mul_assoc]
        rw [h_step1]
        have h_mul2 : ENNReal.ofReal K_global * (9 : ENNReal) = ENNReal.ofReal (K_global * 9) := by
          rw [ENNReal.ofReal_mul hKg_nonneg] <;> norm_cast
        rw [h_mul2]
        have h_comm : K_global * 9 = 9 * K_global := by ring
        rw [h_comm] <;> rfl

  have h_main : IsSquareRootRegular δ_n t (C * K_density) K E' :=
    subset_regular_with_density hReg h_sub hE'_nonempty hK_density_pos h_density
  have h_eq : C * K_density = C * 9 * K_global := by dsimp only [K_density] <;> ring
  rw [h_eq] at h_main
  exact h_main

/-! ========================================================================
   Step 5 (CORRECTED): Retained regularity with explicit loss factor 18.

   CRITICAL: The original skeleton claimed output δ_n^{-(ε-ε/4)} is impossible.
   Retention DEGRADES the constant: C' = C * 18.
   Loss sign must be +loss (more negative exponent), not -loss.
   ======================================================================== -/

/-- Step 5 corrected: retained set regularity with loss factor 18 = 9×2.
    S-set constant: C * 18. Sqrt-scale constant: K (preserved). -/
theorem step5_retained_regularity_corrected
    {n m : ℕ} {hnm : m ≤ n}
    (s t ε : ℝ) (hst : s < t) (hε_pos : 0 < ε)
    (C₁ : ℝ) (M : ℕ)
    (config : CombiningTheorem.NiceConfiguration n s C₁ M)
    (P : Finset (DyadicSquare n))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty : P.Nonempty)
    (h_retention : (P.card : ℝ) ≥ (config.P₀.card : ℝ) / 2)
    {C K : ℝ}
    (hP_original_reg : IsSquareRootRegular (dyadicDelta n) t C K config.pointSet) :
    IsSquareRootRegular (dyadicDelta n) t (C * 18) K
      (⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set Plane)) := by
  have h_global_ret : (config.P₀.card : ℝ) ≤ 2 * (P.card : ℝ) := by
    have h : (P.card : ℝ) ≥ (config.P₀.card : ℝ) / 2 := h_retention
    linarith
  let E' := (⋃ p ∈ (P : Set (DyadicSquare n)), (p.toSet : Set Plane))
  have h : IsSquareRootRegular (dyadicDelta n) t (C * 9 * (2 : ℝ)) K E' :=
    global_retained_regular_clean hP_original_reg P hP_sub 2 (by norm_num) h_global_ret hP_nonempty
  have h92 : C * 9 * (2 : ℝ) = C * 18 := by ring
  rw [h92] at h
  exact h

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
