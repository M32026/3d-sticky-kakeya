module

/-
  Clean square and covering lemmas extracted from Prop73.CoarseSsetConversion
  and FrontEndExtraction.GeometricAndExternal.

  This module provides geometry lemmas that were previously only available
  through contaminated import paths (Prop73 and AppendixA).

  Contains:
  - `ep` — construct EuclideanPlane point from coordinates
  - `squareCenter` — center of a dyadic square
  - `dSquareCorner` — DSquare corner as a EuclideanPlane point
  - `fine_square_subset_coarse` — fine square ⊆ coarse containing square
  - `dyadicSquare_covered_by_center` — square ⊆ ball of radius δ around center
  - `pointSet_ncover_bound` — Ncover(pointSet) ≤ |coarse image of P₀|
  - `ball_intersects_at_most_9_squares` — ball intersects at most 9 dyadic squares

  Whiteprint node: clean_square_lemmas
  Status: COMPLETE
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionOnScales
open DirecretisedFurstenbergEstimate (EuclideanPlane)

attribute [local instance] Classical.propDecidable

/-- If real `a > b - 2` for integers `a, b`, then `b - 1 ≤ a`. -/
lemma int_gt_sub_two_implies_ge_sub_one {a b : ℤ} (h : (a : ℝ) > (b : ℝ) - 2) : b - 1 ≤ a := by
  by_contra h'
  have h'' : a ≤ b - 2 := by omega
  have h''' : (a : ℝ) ≤ (b : ℝ) - 2 := by exact_mod_cast h''
  exact not_lt.mpr h''' h

/-- If real `a < b + 2` for integers `a, b`, then `a ≤ b + 1`. -/
lemma int_lt_add_two_implies_le_add_one {a b : ℤ} (h : (a : ℝ) < (b : ℝ) + 2) : a ≤ b + 1 := by
  by_contra h'
  have h'' : a ≥ b + 2 := by omega
  have h''' : (a : ℝ) ≥ (b : ℝ) + 2 := by exact_mod_cast h''
  exact not_lt.mpr h''' h

/-- Core integer bound logic for ball_intersects_at_most_9_squares, isolated for performance. -/
lemma ball_9_i_bounds (c0 p0 : ℝ) (δ : ℝ) (hδ_pos : 0 < δ)
    (qi : ℤ) (hpi1 : (qi : ℝ) * δ ≤ p0) (hpi2 : p0 < ((qi : ℝ) + 1) * δ)
    (hpi_coord : |p0 - c0| ≤ δ) :
    qi ∈ Finset.Icc (⌊c0 / δ⌋ - 1) (⌊c0 / δ⌋ + 1) := by
  let i0 : ℤ := ⌊c0 / δ⌋
  have h_floor1 : (i0 : ℝ) ≤ c0 / δ := Int.floor_le (c0 / δ)
  have h_floor2 : c0 / δ < (i0 : ℝ) + 1 := Int.lt_floor_add_one (c0 / δ)
  have h1 : p0 ≥ c0 - δ := by
    have h11 : -(δ) ≤ p0 - c0 := (abs_le.mp hpi_coord).1
    linarith
  have h2 : p0 ≤ c0 + δ := by
    have h21 : p0 - c0 ≤ δ := (abs_le.mp hpi_coord).2
    linarith
  have h3_lower : (qi : ℝ) > (i0 : ℝ) - 2 := by
    have h4 : ((qi : ℝ) + 1) * δ > c0 - δ := by
      exact lt_of_le_of_lt h1 hpi2
    have h5 : (qi : ℝ) + 1 > c0 / δ - 1 := by
      have h6 : ((qi : ℝ) + 1) * δ / δ > (c0 - δ) / δ := by gcongr
      have h7 : ((qi : ℝ) + 1) * δ / δ = (qi : ℝ) + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have h8 : (c0 - δ) / δ = c0 / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h7, h8] at h6
      exact h6
    have h9 : (qi : ℝ) > c0 / δ - 2 := by linarith
    linarith [h_floor1]
  have h3_upper : (qi : ℝ) < (i0 : ℝ) + 2 := by
    have h4 : (qi : ℝ) * δ ≤ c0 + δ := by
      exact le_trans hpi1 h2
    have h5 : (qi : ℝ) ≤ c0 / δ + 1 := by
      have h6 : (qi : ℝ) * δ / δ ≤ (c0 + δ) / δ := by gcongr
      have h7 : (qi : ℝ) * δ / δ = (qi : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      have h8 : (c0 + δ) / δ = c0 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h7, h8] at h6
      exact h6
    linarith [h_floor2]
  have h4_lower : i0 - 1 ≤ qi := int_gt_sub_two_implies_ge_sub_one h3_lower
  have h4_upper : qi ≤ i0 + 1 := int_lt_add_two_implies_le_add_one h3_upper
  simp only [Finset.mem_Icc]
  exact ⟨h4_lower, h4_upper⟩

/-- Construct a EuclideanPlane point from coordinates. -/
def ep (x y : ℝ) : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![x, y]

/-- Center of a dyadic square as a EuclideanPlane point. -/
def squareCenter {m : ℕ} (δ : ℝ) (Q : DyadicSquare m) : EuclideanPlane :=
  ep (((Q.i : ℝ) + 1 / 2) * δ) (((Q.j : ℝ) + 1 / 2) * δ)

/-- DSquare corner as a EuclideanPlane point. -/
def dSquareCorner {m : ℕ} (δ : ℝ) (p : DSquare m) : EuclideanPlane :=
  ep ((p.i : ℝ) * δ) ((p.j : ℝ) * δ)

/-- A fine dyadic square is contained in its coarse containing square. -/
lemma fine_square_subset_coarse {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) :
    (p.toSet : Set EuclideanPlane) ⊆
      ((InductionConfigurations.containingSquare hnm p).toSet : Set EuclideanPlane) := by
  let Q := InductionConfigurations.containingSquare hnm p
  have h_cont : InductionConfigurations.squareContained hnm p Q :=
    (squareContained_iff_containingSquare hnm p Q).mpr rfl
  exact squareContained_toSet_subset hnm (h := h_cont)

/-- A dyadic square of side δ is contained in a Euclidean closed ball of radius δ. -/
lemma dyadicSquare_covered_by_center {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (Q : DyadicSquare m) :
    (Q.toSet : Set EuclideanPlane) ⊆ Metric.closedBall (squareCenter δ Q) δ := by
  let c := squareCenter δ Q
  intro x hx
  have hxi1 : (Q.i : ℝ) * dyadicDelta m ≤ x 0 := hx.1
  have hxi2 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta m := hx.2.1
  have hxj1 : (Q.j : ℝ) * dyadicDelta m ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta m := hx.2.2.2
  have h1 : |x 0 - c 0| ≤ δ / 2 := by
    have h4 : c 0 = ((Q.i : ℝ) + 1 / 2) * δ := by simp [c, squareCenter] <;> rfl
    have h7 : (Q.i : ℝ) * δ ≤ x 0 := by
      have h8 : (Q.i : ℝ) * dyadicDelta m = (Q.i : ℝ) * δ := by rw [hδ_eq]
      rw [h8] at hxi1; exact hxi1
    have h9 : x 0 < ((Q.i : ℝ) + 1) * δ := by
      have h10 : ((Q.i : ℝ) + 1) * dyadicDelta m = ((Q.i : ℝ) + 1) * δ := by rw [hδ_eq]
      rw [h10] at hxi2; exact hxi2
    rw [h4]
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h2 : |x 1 - c 1| ≤ δ / 2 := by
    have h4 : c 1 = ((Q.j : ℝ) + 1 / 2) * δ := by simp [c, squareCenter] <;> rfl
    have h7 : (Q.j : ℝ) * δ ≤ x 1 := by
      have h8 : (Q.j : ℝ) * dyadicDelta m = (Q.j : ℝ) * δ := by rw [hδ_eq]
      rw [h8] at hxj1; exact hxj1
    have h9 : x 1 < ((Q.j : ℝ) + 1) * δ := by
      have h10 : ((Q.j : ℝ) + 1) * dyadicDelta m = ((Q.j : ℝ) + 1) * δ := by rw [hδ_eq]
      rw [h10] at hxj2; exact hxj2
    rw [h4]
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h3 : dist x c ≤ δ := by
    have h4 : dist x c ^ 2 = ∑ i : Fin 2, dist (x i) (c i) ^ 2 := EuclideanSpace.dist_sq_eq x c
    have h5 : (∑ i : Fin 2, dist (x i) (c i) ^ 2) = (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 := by
      simp [Fin.sum_univ_two, Real.dist_eq] <;> ring
    have h6 : (x 0 - c 0) ^ 2 ≤ (δ / 2) ^ 2 := by
      have h7 : |x 0 - c 0| ≤ δ / 2 := h1
      calc (x 0 - c 0) ^ 2 = |x 0 - c 0| ^ 2 := by rw [sq_abs]
        _ ≤ (δ / 2) ^ 2 := by gcongr
    have h8 : (x 1 - c 1) ^ 2 ≤ (δ / 2) ^ 2 := by
      have h9 : |x 1 - c 1| ≤ δ / 2 := h2
      calc (x 1 - c 1) ^ 2 = |x 1 - c 1| ^ 2 := by rw [sq_abs]
        _ ≤ (δ / 2) ^ 2 := by gcongr
    have h10 : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 ≤ δ ^ 2 := by nlinarith
    have h11 : dist x c ^ 2 ≤ δ ^ 2 := by rw [h4, h5] <;> exact h10
    have h12 : 0 ≤ dist x c := by positivity
    nlinarith
  exact h3

/-- Ncover(δ, config.pointSet) ≤ |coarse image of config.P₀|. -/
lemma pointSet_ncover_bound
    {k m : ℕ} (hnm : m ≤ k)
    {s C₁ : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration k s C₁ M)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_eq : δ = dyadicDelta m) :
    Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤
      ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ENat) := by
  let coarseSquares := config.P₀.image (InductionConfigurations.containingSquare hnm)
  let centers : Finset EuclideanPlane := coarseSquares.image (fun Q : DyadicSquare m => squareCenter δ Q)
  have h1 : config.pointSet ⊆ ⋃ c ∈ (centers : Set EuclideanPlane), Metric.closedBall c δ.toNNReal := by
    intro x hx
    have h_exists : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ x ∈ (p.toSet : Set EuclideanPlane) := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h_exists with ⟨p, hp, hxp⟩
    let Q := InductionConfigurations.containingSquare hnm p
    have hQ_in : Q ∈ coarseSquares := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    let cQ : EuclideanPlane := squareCenter δ Q
    have hc_in : cQ ∈ centers := Finset.mem_image.mpr ⟨Q, hQ_in, rfl⟩
    have h2 : x ∈ Q.toSet := fine_square_subset_coarse hnm p hxp
    have h3 : x ∈ Metric.closedBall cQ δ := dyadicSquare_covered_by_center hδ_pos hδ_eq Q h2
    have h4 : x ∈ Metric.closedBall cQ δ.toNNReal := by
      have h5 : (δ.toNNReal : ℝ) = δ := by
        simp [NNReal.coe_mk, hδ_pos.le] <;> linarith
      simpa [Metric.mem_closedBall, h5] using h3
    exact Set.mem_iUnion₂.mpr ⟨cQ, hc_in, h4⟩
  have h4 : Metric.IsCover δ.toNNReal config.pointSet (centers : Set EuclideanPlane) :=
    Metric.IsCover.of_subset_iUnion_closedBall h1
  have h5 : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤ (centers : Set EuclideanPlane).encard :=
    h4.externalCoveringNumber_le_encard
  have h6 : (centers : Set EuclideanPlane).encard = (centers.card : ENat) := by simp
  have h7 : centers.card ≤ coarseSquares.card := Finset.card_image_le
  rw [h6] at h5
  exact le_trans h5 (by exact_mod_cast h7)

/-- A Euclidean ball of radius δ intersects at most 9 dyadic squares of side δ. -/
lemma ball_intersects_at_most_9_squares {n : ℕ} (c : EuclideanPlane) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta n) :
    ∃ (I : Finset (DyadicSquare n)), I.card ≤ 9 ∧
      ∀ (q : DyadicSquare n), (q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ ≠ ∅ → q ∈ I := by
  let i0 : ℤ := ⌊c 0 / δ⌋
  let j0 : ℤ := ⌊c 1 / δ⌋
  let indices_i : Finset ℤ := Finset.Icc (i0 - 1) (i0 + 1)
  let indices_j : Finset ℤ := Finset.Icc (j0 - 1) (j0 + 1)
  have h_card3 : ∀ (z : ℤ), (Finset.Icc (z - 1) (z + 1)).card = 3 := by
    intro z
    simp [Finset.Icc_eq_empty_of_lt] <;> omega
  classical
  let I : Finset (DyadicSquare n) :=
    indices_i.biUnion fun i => indices_j.image (fun j => ⟨i, j⟩)
  have h_inj : ∀ (i : ℤ), Function.Injective (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n)) := by
    intro i _ _ h
    simpa [DyadicSquare.mk.injEq] using h
  have hI_card : I.card ≤ 9 := by
    have h1 : I.card ≤ ∑ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card :=
      Finset.card_biUnion_le
    have h2 : ∀ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card = indices_j.card := by
      intro i _
      rw [Finset.card_image_of_injective _ (h_inj i)]
    have h3 : I.card ≤ ∑ i ∈ indices_i, indices_j.card := by
      calc I.card
        ≤ ∑ i ∈ indices_i, (indices_j.image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare n))).card := h1
      _ = ∑ i ∈ indices_i, indices_j.card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h2 i hi
    have h4 : indices_i.card = 3 := h_card3 i0
    have h5 : ∑ i ∈ indices_i, indices_j.card = indices_i.card * indices_j.card := by
      rw [Finset.sum_const] <;> ring
    have h6 : indices_j.card = 3 := h_card3 j0
    have h7 : I.card ≤ 9 := by
      calc I.card ≤ ∑ i ∈ indices_i, indices_j.card := h3
           _ = indices_i.card * indices_j.card := h5
           _ = 3 * indices_j.card := by rw [h4]
           _ = 3 * 3 := by rw [h6]
           _ = 9 := by norm_num
    exact h7
  refine ⟨I, hI_card, ?_⟩
  intro q hq
  have h_nonempty : ((q.toSet : Set EuclideanPlane) ∩ Metric.closedBall c δ).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hq
  rcases h_nonempty with ⟨p, hpQ, hpc⟩
  have hpi1 : (q.i : ℝ) * δ ≤ p 0 := by
    have h : (q.i : ℝ) * dyadicDelta n ≤ p 0 := hpQ.1
    rwa [←hδ_eq] at h
  have hpi2 : p 0 < ((q.i : ℝ) + 1) * δ := by
    have h : p 0 < ((q.i : ℝ) + 1) * dyadicDelta n := hpQ.2.1
    rwa [←hδ_eq] at h
  have hpj1 : (q.j : ℝ) * δ ≤ p 1 := by
    have h : (q.j : ℝ) * dyadicDelta n ≤ p 1 := hpQ.2.2.1
    rwa [←hδ_eq] at h
  have hpj2 : p 1 < ((q.j : ℝ) + 1) * δ := by
    have h : p 1 < ((q.j : ℝ) + 1) * dyadicDelta n := hpQ.2.2.2
    rwa [←hδ_eq] at h
  have hpc' : dist p c ≤ δ := hpc
  have h_coord_bound : ∀ (i : Fin 2), |p i - c i| ≤ dist p c := by
    intro i
    have h1 : dist p c = ‖p - c‖ := by rfl
    rw [h1]
    have h2 : ‖p - c‖ ^ 2 = ((p - c) 0)^2 + ((p - c) 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq (p - c), Fin.sum_univ_two]
    have h3 : ((p - c) i)^2 ≤ ‖p - c‖ ^ 2 := by
      rw [h2]
      fin_cases i <;> simp [Fin.sum_univ_two] <;> nlinarith [sq_nonneg ((p - c) 0), sq_nonneg ((p - c) 1)]
    have h4 : 0 ≤ ‖p - c‖ := by positivity
    have h5 : |(p - c) i| ^ 2 ≤ ‖p - c‖ ^ 2 := by
      have h6 : |(p - c) i| ^ 2 = ((p - c) i)^2 := by rw [sq_abs]
      rw [h6] <;> exact h3
    have h7 : |(p - c) i| ≤ ‖p - c‖ := by
      nlinarith [abs_nonneg ((p - c) i)]
    simpa using h7
  have hpi_coord : |p 0 - c 0| ≤ δ := (h_coord_bound 0).trans hpc'
  have hpj_coord : |p 1 - c 1| ≤ δ := (h_coord_bound 1).trans hpc'
  have hqi_in : q.i ∈ indices_i :=
    ball_9_i_bounds (c 0) (p 0) δ hδ_pos q.i hpi1 hpi2 hpi_coord
  have hqj_in : q.j ∈ indices_j :=
    ball_9_i_bounds (c 1) (p 1) δ hδ_pos q.j hpj1 hpj2 hpj_coord
  have hq_in_I : q ∈ I := by
    simp only [I, Finset.mem_biUnion]
    refine ⟨q.i, hqi_in, ?_⟩
    simpa [Finset.mem_image] using ⟨q.j, hqj_in, rfl⟩
  exact hq_in_I

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
