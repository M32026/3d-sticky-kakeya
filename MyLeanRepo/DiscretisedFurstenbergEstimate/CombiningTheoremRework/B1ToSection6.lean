module

/-
  B1-to-Section6 Production Composition

  Bridges the output of `b1_bridge_decomposition` to the input hypotheses
  consumed by the Section 6 local fiber incidence theorem.

  Key lemmas:
  - `b1_sset_transfer_to_fine`: transfer S-set from original pointSet to
    normalized fiber inside a coarse square, using density + rescaling.

  Whiteprint node: combining_theorem_genuine / b1_to_section6
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.CommonLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.RescaleSsetEuclidean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DirecretisedFurstenbergEstimate.Section6
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DiscretisedFurstenbergEstimate.InductionConfigurations

/-! ### S-set transfer from original pointSet to normalized fine fiber

    Given an S-set on the original pointSet at scale δ_n, a coarse square Q
    at scale δ_m, and a density bound showing the restriction to Q retains
    enough points, transfer the S-set to the normalized fiber (rescaled by
    1/δ_m) at scale δ_{n-m}.

    Uses:
    - `thin_preserves_sset_by_density` for restriction with density
    - `translate_sset_euclidean` for translation to origin
    - `rescale_sset_euclidean` for arbitrary rescaling
-/

/-- Lower-left corner of a dyadic square as a Euclidean plane point. -/
def dyadicSquareLowerLeft {n : ℕ} (p : DyadicSquare n) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 =>
    if i = 0 then (p.i : ℝ) * dyadicDelta n
    else (p.j : ℝ) * dyadicDelta n

/-- Transfer S-set from original pointSet to normalized fiber inside Q.

    Given:
    - `hE`: original pointSet is a (δ_n, t, C)-set
    - `h_density`: covering number of original ≤ K * covering number of restriction to Q
    - `hE'_nonempty`: restriction is nonempty

    Produces: the normalized fiber (translate Q to origin, then scale by 1/δ_m)
    is a (δ_n/δ_m, t, C * K * δ_m^t)-set. -/
lemma b1_sset_transfer_to_fine
    {n m : ℕ} (hnm : m ≤ n)
    {t C K : ℝ} (ht_pos : 0 < t) (hC_pos : 0 < C) (hK_pos : 0 < K)
    {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : IsDeltaSSet (dyadicDelta n) t C E)
    (Q : DyadicSquare m)
    (hE'_nonempty : (E ∩ Q.toSet).Nonempty)
    (h_density : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal E : ENNReal) ≤
                 ENNReal.ofReal K *
                   (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (E ∩ Q.toSet) : ENNReal)) :
    IsDeltaSSet (dyadicDelta n / dyadicDelta m) t
      (C * K * (dyadicDelta m) ^ t)
      ((fun x : EuclideanSpace ℝ (Fin 2) => (dyadicDelta m)⁻¹ • (x + (-dyadicSquareLowerLeft Q))) ''
        (E ∩ Q.toSet)) := by
  let δ_n := dyadicDelta n
  let δ_m := dyadicDelta m
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m
  let E' := E ∩ Q.toSet
  -- Step 1: Restrict E to E' with density factor K
  have h_sub : E' ⊆ E := Set.inter_subset_left
  have hE'_sset : IsDeltaSSet δ_n t (C * K) E' :=
    thin_preserves_sset_by_density hE h_sub hE'_nonempty hK_pos h_density
  -- Step 2: Translate E' by -lowerLeft(Q)
  let v := dyadicSquareLowerLeft Q
  let E_trans := (fun x : EuclideanSpace ℝ (Fin 2) => x + (-v)) '' E'
  have hE_trans_sset : IsDeltaSSet δ_n t (C * K) E_trans :=
    translate_sset_euclidean (hE'_sset)
  -- Step 3: Rescale by c = 1/δ_m
  let c : ℝ := δ_m⁻¹
  have hc_pos : 0 < c := by positivity
  let E_norm := (fun x : EuclideanSpace ℝ (Fin 2) => c • x) '' E_trans
  have hE_norm_sset : IsDeltaSSet (c * δ_n) t ((C * K) * c ^ (-t)) E_norm :=
    rescale_sset_euclidean hc_pos hE_trans_sset
  -- Simplify scale: c * δ_n = δ_n / δ_m
  have h_scale_eq : c * δ_n = δ_n / δ_m := by
    dsimp only [c] <;> field_simp [hδm_pos.ne'] <;> ring
  -- Simplify constant: (C * K) * c^(-t) = C * K * δ_m^t
  have h_const_eq : (C * K) * c ^ (-t) = C * K * δ_m ^ t := by
    dsimp only [c]
    have h1 : c ^ (-t) = δ_m ^ t := by
      have h2 : c = δ_m⁻¹ := by rfl
      rw [h2]
      have h3 : (δ_m⁻¹) ^ (-t) = δ_m ^ t := by
        have h4 : (δ_m⁻¹) ^ (-t) = (δ_m ^ t)⁻¹⁻¹ := by
          rw [Real.inv_rpow (by linarith), Real.rpow_neg (by linarith)] <;> ring
        rw [h4] <;> field_simp [hδm_pos.ne'] <;> ring
      exact h3
    rw [h1] <;> ring
  rw [h_scale_eq, h_const_eq] at hE_norm_sset
  have h_main : E_norm = (fun x : EuclideanSpace ℝ (Fin 2) => (dyadicDelta m)⁻¹ • (x + (-dyadicSquareLowerLeft Q))) '' (E ∩ Q.toSet) := by
    dsimp only [E_norm, E_trans, c, v, E']
    rw [Set.image_image]
    <;> congr
    <;> funext x
    <;> simp [smul_add]
    <;> abel
  rw [h_main] at hE_norm_sset
  exact hE_norm_sset

/-! ### Geometry bounds from B1 bridge hypotheses

    Extract slope, diameter, and unit-coordinate bounds directly from
    `B1BridgeHypotheses` at a configuration's own scale. -/

/-- From `hB1.h_tubes_strip`, derive `|T.slope| ≤ 1` for all tubes. -/
lemma b1_geometry_slope
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : FormatConversion.M2.B1BridgeHypotheses k config) :
    ∀ (T : DyadicTube k), T ∈ config.T₀ → |T.slope| ≤ 1 := by
  intro T hT
  have h_strip : -(2 ^ k : ℤ) ≤ T.a ∧ T.a < (2 ^ k : ℤ) :=
    hB1.h_tubes_strip T hT
  have h1 : -(2 ^ k : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
  have h2 : (T.a : ℝ) < (2 ^ k : ℝ) := by exact_mod_cast h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ k : ℝ) := by
    rw [abs_le] <;> constructor <;> linarith
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta k := by rfl
  have hδ_eq : dyadicDelta k = 1 / (2 ^ k : ℝ) := by
    simp [dyadicDelta] <;> field_simp <;> ring
  rw [h_slope_eq, hδ_eq]
  have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
  have h4 : |(T.a : ℝ) * (1 / (2 ^ k : ℝ))| =
      |(T.a : ℝ)| * (1 / (2 ^ k : ℝ)) := by
    have hpos2 : (0 : ℝ) < (1 / (2 ^ k : ℝ)) := by positivity
    rw [abs_mul, abs_of_pos hpos2]
  rw [h4]
  have h5 : |(T.a : ℝ)| * (1 / (2 ^ k : ℝ)) ≤ 1 := by
    calc |(T.a : ℝ)| * (1 / (2 ^ k : ℝ))
      ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
    _ = 1 := by field_simp [hpos.ne'] <;> ring
  exact h5

/-- From `hB1.h_squares_unit`, derive that all points in all DSquares
    lie in [0,1)². -/
lemma b1_geometry_full_unit
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : FormatConversion.M2.B1BridgeHypotheses k config) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet →
        0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 := by
  intro p hp x hx
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  have h_bounds := hB1.h_squares_unit q hq
  have h_i_nonneg : 0 ≤ (dyadicSquareToDSquare q).i := by
    simpa [dyadicSquareToDSquare] using h_bounds.1
  have h_i_lt : (dyadicSquareToDSquare q).i < (2 ^ k : ℤ) := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.1
  have h_j_nonneg : 0 ≤ (dyadicSquareToDSquare q).j := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.2.1
  have h_j_lt : (dyadicSquareToDSquare q).j < (2 ^ k : ℤ) := by
    simpa [dyadicSquareToDSquare] using h_bounds.2.2.2
  have hδ_eq : δ k = 1 / (2 ^ k : ℝ) := by
    simp [δ, dyadicDelta] <;> field_simp <;> ring
  have hδ_pos : 0 < δ k := δ_pos k
  have h_x1_ge : 0 ≤ x.1 := by
    have h_lo : ((dyadicSquareToDSquare q).i : ℝ) * δ k ≤ x.1 := hx.1
    have h_i0 : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) := by exact_mod_cast h_i_nonneg
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).i : ℝ) * δ k := mul_nonneg h_i0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_i1_le : ((dyadicSquareToDSquare q).i : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : (dyadicSquareToDSquare q).i < (2 ^ k : ℤ) := h_i_lt
    have h' : (dyadicSquareToDSquare q).i + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h'
  have h_x1_lt : x.1 < 1 := by
    have h : x.1 < (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ k := hx.2.1
    have h2 : (((dyadicSquareToDSquare q).i : ℝ) + 1) * δ k ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).i : ℝ) + 1) * (1 / (2 ^ k : ℝ))
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  have h_x2_ge : 0 ≤ x.2 := by
    have h_lo : ((dyadicSquareToDSquare q).j : ℝ) * δ k ≤ x.2 := hx.2.2.1
    have h_j0 : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) := by exact_mod_cast h_j_nonneg
    have h_nonneg : 0 ≤ ((dyadicSquareToDSquare q).j : ℝ) * δ k := mul_nonneg h_j0 (le_of_lt hδ_pos)
    exact le_trans h_nonneg h_lo
  have h_j1_le : ((dyadicSquareToDSquare q).j : ℝ) + 1 ≤ (2 ^ k : ℝ) := by
    have h : (dyadicSquareToDSquare q).j < (2 ^ k : ℤ) := h_j_lt
    have h' : (dyadicSquareToDSquare q).j + 1 ≤ (2 ^ k : ℤ) := by omega
    exact_mod_cast h'
  have h_x2_lt : x.2 < 1 := by
    have h : x.2 < (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ k := hx.2.2.2
    have h2 : (((dyadicSquareToDSquare q).j : ℝ) + 1) * δ k ≤ 1 := by
      rw [hδ_eq]
      have hpos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      calc (((dyadicSquareToDSquare q).j : ℝ) + 1) * (1 / (2 ^ k : ℝ))
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ)) := by gcongr
      _ = 1 := by field_simp [hpos.ne'] <;> ring
    exact lt_of_lt_of_le h h2
  exact ⟨h_x1_ge, h_x1_lt, h_x2_ge, h_x2_lt⟩

/-- From `hB1.h_squares_unit`, derive `|x.1| ≤ 1` for all points in all DSquares. -/
lemma b1_geometry_unit
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : FormatConversion.M2.B1BridgeHypotheses k config) :
    ∀ (p : DSquare k), p ∈ finsetDyadicToDSquare config.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 := by
  have h_full := b1_geometry_full_unit hB1
  intro p hp x hx
  have h := h_full p hp x hx
  have h1 : 0 ≤ x.1 := h.1
  have h2 : x.1 < 1 := h.2.1
  rw [abs_le] <;> constructor <;> linarith

/-- From `hB1.h_squares_unit`, derive `dist p q ≤ 3` for any two DSquares. -/
lemma b1_geometry_diam
    {k : ℕ} {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration k s C₁ M}
    (hB1 : FormatConversion.M2.B1BridgeHypotheses k config) :
    ∀ (p q : DSquare k),
      p ∈ finsetDyadicToDSquare config.P₀ →
      q ∈ finsetDyadicToDSquare config.P₀ → dist p q ≤ 3 := by
  have h_full := b1_geometry_full_unit hB1
  intro p q hp hq
  have h_p_in : p.toPoint ∈ p.toSet := by
    have hδ_pos : 0 < δ k := δ_pos k
    simp only [DSquare.toPoint, DSquare.toSet, Set.mem_setOf_eq]
    have h1 : (p.i : ℝ) * δ k ≤ (p.i : ℝ) * δ k := by rfl
    have h2 : (p.i : ℝ) * δ k < ((p.i : ℝ) + 1) * δ k := by
      have h3 : (p.i : ℝ) < (p.i : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h3 hδ_pos
    have h4 : (p.j : ℝ) * δ k ≤ (p.j : ℝ) * δ k := by rfl
    have h5 : (p.j : ℝ) * δ k < ((p.j : ℝ) + 1) * δ k := by
      have h6 : (p.j : ℝ) < (p.j : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h6 hδ_pos
    exact ⟨h1, h2, h4, h5⟩
  have h_q_in : q.toPoint ∈ q.toSet := by
    have hδ_pos : 0 < δ k := δ_pos k
    simp only [DSquare.toPoint, DSquare.toSet, Set.mem_setOf_eq]
    have h1 : (q.i : ℝ) * δ k ≤ (q.i : ℝ) * δ k := by rfl
    have h2 : (q.i : ℝ) * δ k < ((q.i : ℝ) + 1) * δ k := by
      have h3 : (q.i : ℝ) < (q.i : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h3 hδ_pos
    have h4 : (q.j : ℝ) * δ k ≤ (q.j : ℝ) * δ k := by rfl
    have h5 : (q.j : ℝ) * δ k < ((q.j : ℝ) + 1) * δ k := by
      have h6 : (q.j : ℝ) < (q.j : ℝ) + 1 := by linarith
      exact mul_lt_mul_of_pos_right h6 hδ_pos
    exact ⟨h1, h2, h4, h5⟩
  have hp_bounds := h_full p hp p.toPoint h_p_in
  have hq_bounds := h_full q hq q.toPoint h_q_in
  have h_p1 : 0 ≤ p.toPoint.1 := hp_bounds.1
  have h_p1' : p.toPoint.1 ≤ 1 := le_of_lt hp_bounds.2.1
  have h_p2 : 0 ≤ p.toPoint.2 := hp_bounds.2.2.1
  have h_p2' : p.toPoint.2 ≤ 1 := le_of_lt hp_bounds.2.2.2
  have h_q1 : 0 ≤ q.toPoint.1 := hq_bounds.1
  have h_q1' : q.toPoint.1 ≤ 1 := le_of_lt hq_bounds.2.1
  have h_q2 : 0 ≤ q.toPoint.2 := hq_bounds.2.2.1
  have h_q2' : q.toPoint.2 ≤ 1 := le_of_lt hq_bounds.2.2.2
  have h_dist : dist p q = dist p.toPoint q.toPoint := by rfl
  rw [h_dist]
  have h_sup : dist p.toPoint q.toPoint = max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| := by
    simp [Prod.dist_eq] <;> rfl
  rw [h_sup]
  have h1 : |p.toPoint.1 - q.toPoint.1| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h2 : |p.toPoint.2 - q.toPoint.2| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h_max_le_1 : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 1 :=
    max_le h1 h2
  have h_final : max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2| ≤ 3 := by
    calc max |p.toPoint.1 - q.toPoint.1| |p.toPoint.2 - q.toPoint.2|
      ≤ 1 := h_max_le_1
    _ ≤ 3 := by norm_num
  exact h_final

/-! ### Pigeonhole / heavy square selection (from lagoon) -/

/-- Basic pigeonhole: given a finite family of non-negative real numbers `a i`
    with total at least `N` and index set cardinality at most `K`,
    there exists an index `i` with `a i ≥ N / K`. -/
lemma pigeonhole_average {α : Type*} (s : Finset α) (a : α → ℝ)
    (N K : ℝ) (hN_pos : 0 < N) (hK_pos : 0 < K)
    (h_sum : N ≤ ∑ i ∈ s, a i)
    (h_card : (s.card : ℝ) ≤ K)
    (h_nonneg : ∀ i ∈ s, 0 ≤ a i) :
    ∃ i ∈ s, a i ≥ N / K := by
  by_contra h
  push Not at h
  have h_s_nonempty : s.Nonempty := by
    by_contra h_empty
    have h' : s = ∅ := by simpa using h_empty
    rw [h'] at h_sum
    simp at h_sum <;> linarith
  have h1 : ∑ i ∈ s, a i < ∑ i ∈ s, (N / K) := by
    apply Finset.sum_lt_sum_of_nonempty h_s_nonempty
    intro i hi
    exact h i hi
  have h2 : ∑ i ∈ s, (N / K) = (s.card : ℝ) * (N / K) := by
    simp [Finset.sum_const] <;> ring
  rw [h2] at h1
  have h3 : (s.card : ℝ) * (N / K) ≤ K * (N / K) := by gcongr <;> linarith
  have h4 : K * (N / K) = N := by
    field_simp [hK_pos.ne'] <;> ring
  rw [h4] at h3
  linarith

/-- Composition: from global retention to per-square density.

    Given:
    - `P0_card`: total original point count
    - `s`: set of good coarse squares (e.g. coarseConfig.P₀)
    - `P i`: retained point count in square `i`
    - `h_global_retention`: `P0_card ≤ K_global * Σ_{i ∈ s} P i`
    - `h_card`: `|s| ≤ K_squares`
    - `P i ≤ P0 i` (retained is subset of original)

    Then there exists `i ∈ s` such that:
    `P0_card ≤ K_global * K_squares * P0 i`

    This is the density bound needed by `b1_sset_transfer_to_fine`. -/
lemma density_from_global_retention {α : Type*} (s : Finset α)
    (P0 P : α → ℝ) (P0_card K_global K_squares : ℝ)
    (hP0_pos : 0 < P0_card) (hK_global_pos : 0 < K_global) (hK_sq_pos : 0 < K_squares)
    (h_global_retention : P0_card ≤ K_global * ∑ i ∈ s, P i)
    (h_card : (s.card : ℝ) ≤ K_squares)
    (hP_nonneg : ∀ i ∈ s, 0 ≤ P i)
    (h_subset : ∀ i ∈ s, P i ≤ P0 i) :
    ∃ i ∈ s, P0_card ≤ K_global * K_squares * P0 i := by
  have h_sum : P0_card / K_global ≤ ∑ i ∈ s, P i := by
    have h : P0_card ≤ K_global * ∑ i ∈ s, P i := h_global_retention
    have h' : P0_card / K_global ≤ ∑ i ∈ s, P i := by
      calc P0_card / K_global
        ≤ (K_global * ∑ i ∈ s, P i) / K_global := by gcongr
      _ = ∑ i ∈ s, P i := by
        field_simp [hK_global_pos.ne'] <;> ring
    exact h'
  have hN_pos' : 0 < P0_card / K_global := by positivity
  have h1 : ∃ i ∈ s, P i ≥ (P0_card / K_global) / K_squares :=
    pigeonhole_average s P (P0_card / K_global) K_squares hN_pos' hK_sq_pos h_sum h_card hP_nonneg
  rcases h1 with ⟨i, hi, hPi⟩
  have h2 : P i ≤ P0 i := h_subset i hi
  have h_pos_prod : 0 < K_global * K_squares := mul_pos hK_global_pos hK_sq_pos
  have h4 : (P0_card / K_global) / K_squares = P0_card / (K_global * K_squares) := by
    field_simp [hK_global_pos.ne', hK_sq_pos.ne'] <;> ring
  rw [h4] at hPi
  have h5 : P0_card ≤ K_global * K_squares * P i := by
    have h6 : P0_card / (K_global * K_squares) ≤ P i := hPi
    have h7 : K_global * K_squares * (P0_card / (K_global * K_squares)) = P0_card := by
      field_simp [h_pos_prod.ne'] <;> ring
    have h8 : K_global * K_squares * (P0_card / (K_global * K_squares)) ≤ K_global * K_squares * P i := by gcongr
    rw [h7] at h8
    exact h8
  have h9 : K_global * K_squares * P i ≤ K_global * K_squares * P0 i := by gcongr
  have h10 : P0_card ≤ K_global * K_squares * P0 i := le_trans h5 h9
  exact ⟨i, hi, h10⟩

/-! ### Piece A: Heavy square selection with global retention

    Given B1 decomposition output plus an explicit global retention hypothesis,
    select a coarse square Q with a covering-number density bound.
-/

attribute [local instance] Classical.propDecidable

/-- Lower bound: for fine squares P_Q contained in coarse square Q,
    the δ_n-covering number of their union is at least |P_Q| / 9. -/
lemma pointSet_restrict_ncover_lower
    {n m : ℕ} (hnm : m ≤ n)
    {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M)
    (Q : DyadicSquare m)
    (P_Q : Finset (DyadicSquare n))
    (hP_Q_sub : P_Q ⊆ config.P₀)
    (hP_Q_in_Q : ∀ p ∈ P_Q, InductionConfigurations.squareContained hnm p Q) :
    (P_Q.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (config.pointSet ∩ Q.toSet) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let Plane := EuclideanSpace ℝ (Fin 2)
  have h_main : ∀ (C : Set Plane), Metric.IsCover δ.toNNReal (config.pointSet ∩ Q.toSet) C →
      (P_Q.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set Plane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : Plane) : Finset (DyadicSquare n) :=
        P_Q.filter (fun p => (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases ball_intersects_at_most_9_squares c δ hδ_pos rfl with ⟨I, hI9, hI_mem⟩
        have h4 : Q_c c ⊆ I := by
          intro p hp
          have h5 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ :=
            (Finset.mem_filter.mp hp).2
          exact hI_mem p h5
        have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
        have h6 : I.card ≤ 9 := hI9
        linarith
      have h4 : P_Q ⊆ Cfin.biUnion Q_c := by
        intro p hp
        have h5 : p ∈ config.P₀ := hP_Q_sub hp
        have h6 : (p.toSet : Set Plane) ⊆ config.pointSet := by
          intro z hz
          exact Set.mem_iUnion₂.mpr ⟨p, h5, hz⟩
        have h7 : InductionConfigurations.containingSquare hnm p = Q :=
          (InductionConfigurations.containingSquare_iff hnm p Q).mpr (hP_Q_in_Q p hp)
        have h8 : (p.toSet : Set Plane) ⊆ Q.toSet := by
          have h9 : (p.toSet : Set Plane) ⊆ (InductionConfigurations.containingSquare hnm p).toSet :=
            fine_square_subset_coarse hnm p
          rw [h7] at h9
          exact h9
        have h10 : (p.toSet : Set Plane).Nonempty := by
          let z0 : Plane := WithLp.toLp 2 ![((p.i : ℝ) * δ), ((p.j : ℝ) * δ)]
          have hz01 : (p.i : ℝ) * δ ≤ z0 0 := by simp [z0]
          have hz02 : z0 0 < ((p.i : ℝ) + 1) * δ := by
            simp [z0]
            have h : (p.i : ℝ) < (p.i : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_right h hδ_pos
          have hz03 : (p.j : ℝ) * δ ≤ z0 1 := by simp [z0]
          have hz04 : z0 1 < ((p.j : ℝ) + 1) * δ := by
            simp [z0]
            have h : (p.j : ℝ) < (p.j : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_right h hδ_pos
          have hz0 : z0 ∈ (p.toSet : Set Plane) := by
            simp only [DyadicSquare.toSet, Set.mem_setOf_eq]
            exact ⟨hz01, hz02, hz03, hz04⟩
          exact ⟨z0, hz0⟩
        rcases h10 with ⟨z, hz⟩
        have hz1 : z ∈ config.pointSet := h6 hz
        have hz2 : z ∈ Q.toSet := h8 hz
        have hz3 : z ∈ config.pointSet ∩ Q.toSet := ⟨hz1, hz2⟩
        have h10 : z ∈ ⋃ c ∈ (Cfin : Set Plane), Metric.closedBall c δ.toNNReal := by
          have h11 : z ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal := hC.subset_iUnion_closedBall hz3
          have h2' : C = (Cfin : Set Plane) := h2.symm
          rw [h2'] at h11
          exact h11
        rcases Set.mem_iUnion₂.mp h10 with ⟨c, hc, hzc⟩
        have h10 : Set.Nonempty ((p.toSet : Set Plane) ∩ Metric.closedBall c δ.toNNReal) := ⟨z, hz, hzc⟩
        have h11 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have h13 : (δ.toNNReal : ℝ) = δ := by
            have h14 : 0 ≤ δ := by linarith
            simp [Real.toNNReal, h14]
          have h14 : Metric.closedBall c δ.toNNReal = Metric.closedBall c δ := by
            congr
            <;> exact h13
          have h15 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ.toNNReal ≠ ∅ := h10.ne_empty
          rw [h14] at h15
          exact h15
        exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hp, h11⟩⟩
      have h5 : P_Q.card ≤ ∑ c ∈ Cfin, (Q_c c).card := by
        calc P_Q.card
          ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
        _ ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
      have h6 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact h3 c hc
      have h7 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      have h8 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by
        exact_mod_cast h5.trans h6
      have h9 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h10 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h10] <;> norm_cast
      rw [h9]
      calc (P_Q.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (P_Q.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber δ.toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((P_Q.card : ENNReal) / 9) * 9 ≤ (Metric.externalCoveringNumber δ.toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) * 9 := by gcongr
  have h6 : ((P_Q.card : ENNReal) / 9) * 9 = (P_Q.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber δ.toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) * 9 =
        (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Piece A main theorem: heavy square selection with covering-number density bound.

    Given B1 decomposition output plus explicit global retention,
    select Q ∈ coarseConfig.P₀ such that:
    Ncover_δn(config.pointSet) ≤ (9 * K_global * |coarseConfig.P₀|) * Ncover_δn(config.pointSet ∩ Q.toSet)

    This density bound feeds directly into `b1_sset_transfer_to_fine`.

    Note: The constant |coarseConfig.P₀| can be replaced by any polynomial upper bound
    (e.g. 2^{2m} = δ_m^{-2}) when available. -/
lemma b1_heavy_square_density
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    {K K_global : ℝ}
    {P : Finset (DyadicSquare n)}
    {CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CombiningTheorem.NiceConfiguration m s CΔ MΔ}
    (hK_pos : 0 < K)
    (hK_global_pos : 0 < K_global)
    (hP_nonempty : P.Nonempty)
    (hP_sub : P ⊆ config.P₀)
    (h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_per_Q_ret : ∀ Q ∈ coarseConfig.P₀,
        ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≤
        K * ((P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ))
    (h_global_ret : (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ)) :
    ∃ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.P₀),
      (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) *
      (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (config.pointSet ∩ Q.toSet) : ENNReal) := by
  classical
  let P0 (Q : DyadicSquare m) : ℝ :=
    (config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card
  let P_ret (Q : DyadicSquare m) : ℝ :=
    (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card
  -- Sum of retained per-square counts equals total retained count
  have h_mapsTo : (P : Set (DyadicSquare n)).MapsTo (InductionConfigurations.containingSquare hnm) (coarseConfig.P₀ : Set (DyadicSquare m)) := by
    intro p hp
    have h1 : InductionConfigurations.containingSquare hnm p ∈ P.image (InductionConfigurations.containingSquare hnm) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [h_coarse_P_eq] at *
    <;> exact h1
  have h_sum_filters : P.card = ∑ Q ∈ coarseConfig.P₀, (P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card :=
    Finset.card_eq_sum_card_fiberwise h_mapsTo
  have h_sum : ∑ Q ∈ coarseConfig.P₀, P_ret Q = (P.card : ℝ) := by
    have h1 : ∀ Q ∈ coarseConfig.P₀,
        (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)) =
        P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q) := by
      intro Q _
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter]
      <;> rw [(InductionConfigurations.containingSquare_iff hnm p Q).symm]
    have h2 : ∑ Q ∈ coarseConfig.P₀, P_ret Q = ∑ Q ∈ coarseConfig.P₀, ((P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have h3 : P_ret Q = ((P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) := by
        rw [show P_ret Q = ((P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) from rfl, h1 Q hQ]
        <;> rfl
      exact h3
    rw [h2]
    have h4 : ∑ Q ∈ coarseConfig.P₀, ((P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) = (P.card : ℝ) := by
      have h5 : (P.card : ℝ) = ∑ Q ∈ coarseConfig.P₀, ((P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) := by
        exact_mod_cast h_sum_filters
      exact h5.symm
    exact h4
  have h_configP0_nonempty : config.P₀.Nonempty := hP_nonempty.mono hP_sub
  have hP0_pos : 0 < (config.P₀.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h_configP0_nonempty
  have h_coarse_nonempty : coarseConfig.P₀.Nonempty := by
    rw [h_coarse_P_eq]
    exact hP_nonempty.image _
  have hK_sq_pos : 0 < (coarseConfig.P₀.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h_coarse_nonempty
  -- Apply density_from_global_retention
  have h_heavy : ∃ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ ∧
      (config.P₀.card : ℝ) ≤ K_global * (coarseConfig.P₀.card : ℝ) * P0 Q :=
    density_from_global_retention coarseConfig.P₀ P0 P_ret (config.P₀.card : ℝ) K_global
      (coarseConfig.P₀.card : ℝ) hP0_pos hK_global_pos hK_sq_pos
      (by rw [h_sum] <;> exact h_global_ret)
      (by linarith)
      (fun _ _ => by positivity)
      (fun Q _ => by
        have h : (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card ≤
            (config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hP_sub)
        have h' : (P_ret Q : ℝ) ≤ (P0 Q : ℝ) := by
          dsimp only [P_ret, P0]
          exact_mod_cast h
        exact h')
  rcases h_heavy with ⟨Q, hQ, h_density_count⟩
  -- Upper bound: Ncover(full) ≤ |config.P₀|
  let hnm' : n ≤ n := by linarith
  have h_refine_one : InductionConfigurations.refinementFactor n n = 1 := by
    simp [InductionConfigurations.refinementFactor] <;> omega
  have h_containing_id : ∀ (p : DyadicSquare n),
      InductionConfigurations.containingSquare hnm' p = p := by
    intro p
    simp [InductionConfigurations.containingSquare, h_refine_one] <;> ext <;> omega
  have h_img_id : config.P₀.image (InductionConfigurations.containingSquare hnm') = config.P₀ := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [h_containing_id y]
      exact hy
    · intro hx
      exact ⟨x, hx, h_containing_id x⟩
  have h_upper : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      (config.P₀.card : ENNReal) := by
    have h := pointSet_ncover_bound hnm' config (dyadicDelta_pos n) rfl
    rw [h_img_id] at h
    exact_mod_cast h
  -- Lower bound: |P0 Q| ≤ 9 * Ncover(restrict)
  let P_Q := config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)
  have hP_Q_sub : P_Q ⊆ config.P₀ := Finset.filter_subset _ _
  have hP_Q_in_Q : ∀ p ∈ P_Q, InductionConfigurations.squareContained hnm p Q := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_lower : (P_Q.card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal (config.pointSet ∩ Q.toSet) :=
    pointSet_restrict_ncover_lower hnm config Q P_Q hP_Q_sub hP_Q_in_Q
  -- Combine
  have hP0_eq : P0 Q = (P_Q.card : ℝ) := by rfl
  have h_const_pos : 0 < 9 * K_global * (coarseConfig.P₀.card : ℝ) := by positivity
  have h_density_ENNReal : ENNReal.ofReal (config.P₀.card : ℝ) ≤
      ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * P0 Q) := by
    have h_pos : 0 ≤ K_global * (coarseConfig.P₀.card : ℝ) * P0 Q := by positivity
    exact ENNReal.ofReal_le_ofReal h_density_count
  have h_lower' : ENNReal.ofReal (P0 Q) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal (config.pointSet ∩ Q.toSet) := by
    have h5 : ENNReal.ofReal (P0 Q) = (P_Q.card : ENNReal) := by
      rw [hP0_eq] <;> norm_cast
    rw [h5]
    exact h_lower
  have h3 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * (9 : ENNReal) =
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) := by
    have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
    have h10 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * (9 : ENNReal) =
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal (9 : ℝ) := by
      rw [h9]
    rw [h10]
    have h11 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal (9 : ℝ) =
        ENNReal.ofReal ((K_global * (coarseConfig.P₀.card : ℝ)) * 9) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h11]
    have h12 : (K_global * (coarseConfig.P₀.card : ℝ)) * 9 = 9 * K_global * (coarseConfig.P₀.card : ℝ) := by ring
    rw [h12]
  let Ncover_local := Metric.externalCoveringNumber (dyadicDelta n).toNNReal (config.pointSet ∩ Q.toSet)
  have h_main : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) * Ncover_local := by
    have h_step1 : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * P0 Q) := by
      calc (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal)
        ≤ (config.P₀.card : ENNReal) := h_upper
      _ = ENNReal.ofReal (config.P₀.card : ℝ) := by norm_cast
      _ ≤ ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * P0 Q) := h_density_ENNReal
    have h_step2 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * P0 Q) =
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal (P0 Q) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> ring
    have h_step3 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal (P0 Q) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ((9 : ENNReal) * Ncover_local) := by
      exact mul_le_mul_left' h_lower' _
    have h_step4 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ((9 : ENNReal) * Ncover_local) =
        (ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * (9 : ENNReal)) * Ncover_local := by
      rw [mul_assoc]
    rw [h_step4] at h_step3
    rw [h3] at h_step3
    have h_step2' : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * P0 Q) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal (P0 Q) := by
      rw [h_step2]
    exact le_trans h_step1 (le_trans h_step2' h_step3)
  exact ⟨Q, hQ, h_main⟩

/-! ### Retained-fiber density theorem

    OS Theorem 6.1 needs density on the RETAINED fiber, not the original fiber.
    Given global retention |P₀| ≤ K_global · |P|, select a coarse square Q where
    the retained fiber E_ret(Q) has enough covering-number density.
-/

/-- General lower bound: for any finite family of fine dyadic squares P_Q,
    the δ_n-covering number of their union is at least |P_Q| / 9. -/
lemma finset_squares_ncover_lower
    {n : ℕ} (P_Q : Finset (DyadicSquare n)) :
    (P_Q.card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set (EuclideanSpace ℝ (Fin 2)))) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let Plane := EuclideanSpace ℝ (Fin 2)
  let E := (⋃ p ∈ (P_Q : Set (DyadicSquare n)), (p.toSet : Set Plane))
  have h_main : ∀ (C : Set Plane), Metric.IsCover δ.toNNReal E C →
      (P_Q.card : ENNReal) / 9 ≤ (C.encard : ENNReal) := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set Plane) = C := Set.Finite.coe_toFinset _
      let Q_c (c : Plane) : Finset (DyadicSquare n) :=
        P_Q.filter (fun p => (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅)
      have h3 : ∀ c ∈ Cfin, (Q_c c).card ≤ 9 := by
        intro c _
        rcases ball_intersects_at_most_9_squares c δ hδ_pos rfl with ⟨I, hI9, hI_mem⟩
        have h4 : Q_c c ⊆ I := by
          intro p hp
          have h5 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ :=
            (Finset.mem_filter.mp hp).2
          exact hI_mem p h5
        have h5 : (Q_c c).card ≤ I.card := Finset.card_le_card h4
        have h6 : I.card ≤ 9 := hI9
        linarith
      have h4 : P_Q ⊆ Cfin.biUnion Q_c := by
        intro p hp
        have h10 : (p.toSet : Set Plane).Nonempty := by
          let z0 : Plane := WithLp.toLp 2 ![((p.i : ℝ) * δ), ((p.j : ℝ) * δ)]
          have hz01 : (p.i : ℝ) * δ ≤ z0 0 := by simp [z0]
          have hz02 : z0 0 < ((p.i : ℝ) + 1) * δ := by
            simp [z0]
            have h : (p.i : ℝ) < (p.i : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_right h hδ_pos
          have hz03 : (p.j : ℝ) * δ ≤ z0 1 := by simp [z0]
          have hz04 : z0 1 < ((p.j : ℝ) + 1) * δ := by
            simp [z0]
            have h : (p.j : ℝ) < (p.j : ℝ) + 1 := by linarith
            exact mul_lt_mul_of_pos_right h hδ_pos
          have hz0 : z0 ∈ (p.toSet : Set Plane) := by
            simp only [DyadicSquare.toSet, Set.mem_setOf_eq]
            exact ⟨hz01, hz02, hz03, hz04⟩
          exact ⟨z0, hz0⟩
        rcases h10 with ⟨z, hz⟩
        have hz_in_E : z ∈ E := by
          exact Set.mem_iUnion₂.mpr ⟨p, hp, hz⟩
        have h10 : z ∈ ⋃ c ∈ (Cfin : Set Plane), Metric.closedBall c δ.toNNReal := by
          have h11 : z ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal := hC.subset_iUnion_closedBall hz_in_E
          have h2' : C = (Cfin : Set Plane) := h2.symm
          rw [h2'] at h11
          exact h11
        rcases Set.mem_iUnion₂.mp h10 with ⟨c, hc, hzc⟩
        have h10 : Set.Nonempty ((p.toSet : Set Plane) ∩ Metric.closedBall c δ.toNNReal) := ⟨z, hz, hzc⟩
        have h11 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ ≠ ∅ := by
          have h13 : (δ.toNNReal : ℝ) = δ := by
            have h14 : 0 ≤ δ := by linarith
            simp [Real.toNNReal, h14]
          have h14 : Metric.closedBall c δ.toNNReal = Metric.closedBall c δ := by
            congr <;> exact h13
          have h15 : (p.toSet : Set Plane) ∩ Metric.closedBall c δ.toNNReal ≠ ∅ := h10.ne_empty
          rw [h14] at h15
          exact h15
        exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hp, h11⟩⟩
      have h5 : P_Q.card ≤ ∑ c ∈ Cfin, (Q_c c).card := by
        calc P_Q.card
          ≤ (Cfin.biUnion Q_c).card := Finset.card_le_card h4
        _ ≤ ∑ c ∈ Cfin, (Q_c c).card := Finset.card_biUnion_le
      have h6 : ∑ c ∈ Cfin, (Q_c c).card ≤ ∑ c ∈ Cfin, (9 : ℕ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact h3 c hc
      have h7 : ∑ c ∈ Cfin, (9 : ℕ) = 9 * Cfin.card := by
        simp [Finset.sum_const] <;> ring
      rw [h7] at h6
      have h8 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by
        exact_mod_cast h5.trans h6
      have h9 : (C.encard : ENNReal) = (Cfin.card : ENNReal) := by
        have h10 : C.encard = (Cfin.card : ENat) := by rw [←h2]; simp
        rw [h10] <;> norm_cast
      rw [h9]
      calc (P_Q.card : ENNReal) / 9
        ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
      _ = (Cfin.card : ENNReal) := by
        have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  have h4 : (P_Q.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by
    simpa [Metric.externalCoveringNumber] using le_iInf₂ h_main
  have h5 : ((P_Q.card : ENNReal) / 9) * 9 ≤ (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) * 9 := by gcongr
  have h6 : ((P_Q.card : ENNReal) / 9) * 9 = (P_Q.card : ENNReal) := by
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have h7 : (P_Q.card : ENNReal) ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by
    have h8 : (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) * 9 =
        (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal E : ENNReal) := by ring
    rw [h8] at h5
    rw [h6] at h5
    exact h5
  exact h7

/-- Retained-fiber heavy square density theorem.

    Given B1 decomposition output plus explicit global retention,
    select Q ∈ coarseConfig.P₀ such that:
    Ncover_δn(config.pointSet) ≤ (9 * K_global * |coarseConfig.P₀|) * Ncover_δn(E_ret(Q))

    where E_ret(Q) = ⋃ {p.toSet : p ∈ P, parent(p) = Q}.

    This is the retained-fiber version needed by OS Theorem 6.1. -/
lemma b1_retained_fiber_density
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    {K_global : ℝ}
    {P : Finset (DyadicSquare n)}
    {CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CombiningTheorem.NiceConfiguration m s CΔ MΔ}
    (hK_global_pos : 0 < K_global)
    (hP_nonempty : P.Nonempty)
    (hP_sub : P ⊆ config.P₀)
    (h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_global_ret : (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ)) :
    ∃ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.P₀),
      (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal
        (⋃ p ∈ (P.filter (fun p => InductionConfigurations.squareContained hnm p Q) : Set (DyadicSquare n)),
          (p.toSet : Set (EuclideanSpace ℝ (Fin 2)))) := by
  classical
  let P_ret (Q : DyadicSquare m) : Finset (DyadicSquare n) :=
    P.filter (fun p => InductionConfigurations.squareContained hnm p Q)
  -- Sum of retained per-square counts equals total retained count
  have h_mapsTo : (P : Set (DyadicSquare n)).MapsTo (InductionConfigurations.containingSquare hnm) (coarseConfig.P₀ : Set (DyadicSquare m)) := by
    intro p hp
    have h1 : InductionConfigurations.containingSquare hnm p ∈ P.image (InductionConfigurations.containingSquare hnm) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [h_coarse_P_eq] at *
    <;> exact h1
  have h_sum_filters : P.card = ∑ Q ∈ coarseConfig.P₀, (P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card :=
    Finset.card_eq_sum_card_fiberwise h_mapsTo
  have h_sum : ∑ Q ∈ coarseConfig.P₀, (P_ret Q).card = P.card := by
    have h1 : ∀ Q ∈ coarseConfig.P₀,
        (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)) =
        P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q) := by
      intro Q _
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter]
      <;> rw [(InductionConfigurations.containingSquare_iff hnm p Q).symm]
    have h2 : ∑ Q ∈ coarseConfig.P₀, (P_ret Q).card = ∑ Q ∈ coarseConfig.P₀, (P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have h3 : (P_ret Q) = P.filter (fun p => InductionConfigurations.containingSquare hnm p = Q) := h1 Q hQ
      rw [h3]
    rw [h2]
    exact h_sum_filters.symm
  have h_coarse_nonempty : coarseConfig.P₀.Nonempty := by
    rw [h_coarse_P_eq]
    exact hP_nonempty.image _
  have hK_sq_pos : 0 < (coarseConfig.P₀.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr h_coarse_nonempty
  have hP_pos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP_nonempty
  -- Pigeonhole: some Q has |P_ret Q| ≥ |P| / |coarseConfig.P₀|
  let a : DyadicSquare m → ℝ := fun Q => (P_ret Q).card
  have h_sum_a : (P.card : ℝ) ≤ ∑ i ∈ coarseConfig.P₀, a i := by
    have h1 : ∑ i ∈ coarseConfig.P₀, a i = ∑ Q ∈ coarseConfig.P₀, ((P_ret Q).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Q _
      rfl
    have h2 : ∑ Q ∈ coarseConfig.P₀, ((P_ret Q).card : ℝ) = ↑(∑ Q ∈ coarseConfig.P₀, (P_ret Q).card) := by
      rw [← Nat.cast_sum] <;> rfl
    have h3 : ↑(∑ Q ∈ coarseConfig.P₀, (P_ret Q).card) = (P.card : ℝ) := by
      rw [h_sum] <;> norm_cast
    have h4 : ∑ i ∈ coarseConfig.P₀, a i = (P.card : ℝ) := by
      rw [h1, h2, h3]
    linarith
  have h_heavy : ∃ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ ∧
      (P.card : ℝ) ≤ (coarseConfig.P₀.card : ℝ) * (P_ret Q).card := by
    have h_avg : ∃ Q ∈ coarseConfig.P₀, a Q ≥ (P.card : ℝ) / (coarseConfig.P₀.card : ℝ) :=
      pigeonhole_average coarseConfig.P₀ a
        (P.card : ℝ) (coarseConfig.P₀.card : ℝ)
        hP_pos hK_sq_pos h_sum_a (by linarith) (fun _ _ => by positivity)
    rcases h_avg with ⟨Q, hQ, hge⟩
    have h9 : (P.card : ℝ) ≤ (coarseConfig.P₀.card : ℝ) * (P_ret Q).card := by
      have h10 : (P.card : ℝ) / (coarseConfig.P₀.card : ℝ) ≤ (P_ret Q).card := hge
      have h11 : (coarseConfig.P₀.card : ℝ) * ((P.card : ℝ) / (coarseConfig.P₀.card : ℝ)) = (P.card : ℝ) := by
        field_simp [hK_sq_pos.ne'] <;> ring
      have h12 : (coarseConfig.P₀.card : ℝ) * ((P.card : ℝ) / (coarseConfig.P₀.card : ℝ)) ≤ (coarseConfig.P₀.card : ℝ) * (P_ret Q).card := by gcongr
      rw [h11] at h12
      exact h12
    exact ⟨Q, hQ, h9⟩
  rcases h_heavy with ⟨Q, hQ, h_density_count⟩
  -- Upper bound: Ncover(full) ≤ |config.P₀|
  let hnm' : n ≤ n := by linarith
  have h_refine_one : InductionConfigurations.refinementFactor n n = 1 := by
    simp [InductionConfigurations.refinementFactor] <;> omega
  have h_containing_id : ∀ (p : DyadicSquare n),
      InductionConfigurations.containingSquare hnm' p = p := by
    intro p
    simp [InductionConfigurations.containingSquare, h_refine_one] <;> ext <;> omega
  have h_img_id : config.P₀.image (InductionConfigurations.containingSquare hnm') = config.P₀ := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [h_containing_id y]
      exact hy
    · intro hx
      exact ⟨x, hx, h_containing_id x⟩
  have h_upper : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      (config.P₀.card : ENNReal) := by
    have h := pointSet_ncover_bound hnm' config (dyadicDelta_pos n) rfl
    rw [h_img_id] at h
    exact_mod_cast h
  -- Lower bound: |P_ret Q| ≤ 9 * Ncover(E_ret(Q))
  let E_ret_Q := (⋃ p ∈ (P_ret Q : Set (DyadicSquare n)), (p.toSet : Set (EuclideanSpace ℝ (Fin 2))))
  have h_lower : ((P_ret Q).card : ENNReal) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal E_ret_Q :=
    finset_squares_ncover_lower (P_ret Q)
  -- Combine
  have h_const_pos : 0 < 9 * K_global * (coarseConfig.P₀.card : ℝ) := by positivity
  have h_density_ENNReal : ENNReal.ofReal (config.P₀.card : ℝ) ≤
      ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card) := by
    have h_pos : 0 ≤ K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card := by positivity
    have h13 : (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ) := h_global_ret
    have h14 : K_global * (P.card : ℝ) ≤ K_global * ((coarseConfig.P₀.card : ℝ) * (P_ret Q).card) := by
      gcongr <;> exact h_density_count
    have h15 : (config.P₀.card : ℝ) ≤ K_global * ((coarseConfig.P₀.card : ℝ) * (P_ret Q).card) := le_trans h13 h14
    have h16 : K_global * ((coarseConfig.P₀.card : ℝ) * (P_ret Q).card) = K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card := by ring
    rw [h16] at h15
    exact ENNReal.ofReal_le_ofReal h15
  have h_lower' : ENNReal.ofReal ((P_ret Q).card : ℝ) ≤ (9 : ENNReal) *
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal E_ret_Q := by
    have h5 : ENNReal.ofReal ((P_ret Q).card : ℝ) = ((P_ret Q).card : ENNReal) := by norm_cast
    rw [h5]
    exact h_lower
  have h3 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * (9 : ENNReal) =
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) := by
    have h9 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
    rw [h9]
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
  let Ncover_local := Metric.externalCoveringNumber (dyadicDelta n).toNNReal E_ret_Q
  have h_main : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
      ENNReal.ofReal (9 * K_global * (coarseConfig.P₀.card : ℝ)) * Ncover_local := by
    have h_step1 : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card) := by
      calc (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal)
        ≤ (config.P₀.card : ENNReal) := h_upper
      _ = ENNReal.ofReal (config.P₀.card : ℝ) := by norm_cast
      _ ≤ ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card) := h_density_ENNReal
    have h_step2 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card) =
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal ((P_ret Q).card : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h_step3 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal ((P_ret Q).card : ℝ) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ((9 : ENNReal) * Ncover_local) := by
      exact mul_le_mul_left' h_lower' _
    have h_step4 : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ((9 : ENNReal) * Ncover_local) =
        (ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * (9 : ENNReal)) * Ncover_local := by
      rw [mul_assoc]
    rw [h_step4] at h_step3
    rw [h3] at h_step3
    have h_step2' : ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ) * (P_ret Q).card) ≤
        ENNReal.ofReal (K_global * (coarseConfig.P₀.card : ℝ)) * ENNReal.ofReal ((P_ret Q).card : ℝ) := by
      rw [h_step2]
    exact le_trans h_step1 (le_trans h_step2' h_step3)
  dsimp only [Ncover_local, E_ret_Q] at h_main
  exact ⟨Q, hQ, h_main⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
