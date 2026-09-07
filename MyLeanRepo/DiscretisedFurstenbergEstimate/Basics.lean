module

/-
  Basic properties of `IsDeltaSSet`, discretized Frostman measures,
  Riesz energy, and the Kaufman projection lemma statement.

  ## Main results

  - `IsDeltaSSet.scale_const`, `IsDeltaSSet.refine`
  - `IsDeltaSSet.frostmanMeasure`: existence of a probability measure with ball growth
  - `rieszEnergy`: definition and basic monotonicity
  - `kaufmanProjectionLemma`: statement (deep result, not proved here)

  ## Note on subset preservation

  `IsDeltaSSet.mono` with the *same* constant is false in general.
  A subset can have a much smaller covering number, making the relative
  bound stronger. Use `IsDeltaSSet.refine` with an explicit comparison
  factor `K`.

  Whiteprint node: `basics`
  Dependencies: target file (`IsDeltaSSet`, `AffineLine`, `EuclideanPlane`)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

variable {X : Type*} [PseudoMetricSpace X]

/-! ### Basic properties of `IsDeltaSSet` -/

/-- Scaling the constant upward preserves the property. -/
lemma IsDeltaSSet.scale_const {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC : C ≤ C') :
    IsDeltaSSet δ s C' P := by
  have h1 : P.Nonempty := h.1
  have h2 : 0 < δ := h.2.1
  have h3 : 0 < C' := by linarith [h.2.2.1]
  have h4 : 0 ≤ s := h.2.2.2.1
  have h5 : ∀ (x : X), ∀ (r : ℝ), δ ≤ r →
      (externalCoveringNumber δ.toNNReal (P ∩ closedBall x r) : ℝ≥0∞) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by
    intro x r hr
    have h6 := h.2.2.2.2 x r hr
    calc
      (externalCoveringNumber δ.toNNReal (P ∩ closedBall x r) : ℝ≥0∞)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := h6
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
              (externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by
        gcongr
        <;> exact ENNReal.ofReal_le_ofReal hC
  exact ⟨h1, h2, h3, h4, h5⟩

/-- If `P' ⊆ P` and the covering number of `P` is at most `K` times that of `P'`,
then `P'` is a `(δ, s, C * K)`-set. -/
lemma IsDeltaSSet.refine {δ s C : ℝ} {P P' : Set X} {K : ℝ}
    (h : IsDeltaSSet δ s C P) (hP' : P' ⊆ P) (hP'ne : P'.Nonempty)
    (hK_pos : 0 < K)
    (hcov : (externalCoveringNumber δ.toNNReal P : ℝ≥0∞) ≤
      ENNReal.ofReal K * (externalCoveringNumber δ.toNNReal P' : ℝ≥0∞)) :
    IsDeltaSSet δ s (C * K) P' := by
  have hδ : 0 < δ := h.2.1
  have hCpos : 0 < C := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have hCKpos : 0 < C * K := mul_pos hCpos hK_pos
  have hCnonneg : 0 ≤ C := by linarith
  refine' ⟨hP'ne, hδ, hCKpos, hs, _⟩
  intro x r hr
  have h6 : P' ∩ closedBall x r ⊆ P ∩ closedBall x r := by gcongr
  have h7 : (externalCoveringNumber δ.toNNReal (P' ∩ closedBall x r) : ENNReal) ≤
             (externalCoveringNumber δ.toNNReal (P ∩ closedBall x r) : ENNReal) := by
    exact_mod_cast externalCoveringNumber_mono_set h6
  have h8 := h.2.2.2.2 x r hr
  have h9 : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
    rw [← ENNReal.ofReal_mul hCnonneg]
  calc
    (externalCoveringNumber δ.toNNReal (P' ∩ closedBall x r) : ENNReal)
      ≤ (externalCoveringNumber δ.toNNReal (P ∩ closedBall x r) : ENNReal) := h7
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (externalCoveringNumber δ.toNNReal P : ENNReal) := h8
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (ENNReal.ofReal K * (externalCoveringNumber δ.toNNReal P' : ENNReal)) := by
      gcongr <;> exact hcov
    _ = ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s *
          (externalCoveringNumber δ.toNNReal P' : ENNReal) := by
      have h10 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (ENNReal.ofReal K * (externalCoveringNumber δ.toNNReal P' : ENNReal)) =
          (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s *
            (externalCoveringNumber δ.toNNReal P' : ENNReal) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h10, h9]

/-! ### Discretized Frostman measure -/

/-- For any `a ∈ [-δ, δ]`, there exists `k ∈ Fin 3` such that
`|a - (2k-2)δ/3| ≤ δ/3`. Used to construct a 3×3 grid cover. -/
lemma round_to_grid {a δ : ℝ} (hδ : 0 ≤ δ) (h : |a| ≤ δ) :
    ∃ (k : Fin 3), |a - (2 * (k : ℝ) - 2) * δ / 3| ≤ δ / 3 := by
  by_cases hδ0 : δ = 0
  · subst hδ0
    have h0 : |a| ≤ 0 := h
    have ha : a = 0 := by
      have h1 : -0 ≤ a ∧ a ≤ 0 := abs_le.mp h0
      linarith
    refine ⟨(0 : Fin 3), ?_⟩
    rw [ha] <;> norm_num
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  have h1 : -δ ≤ a := (abs_le.mp h).1
  have h2 : a ≤ δ := (abs_le.mp h).2
  by_cases h3 : a ≤ -δ / 3
  · refine ⟨(0 : Fin 3), ?_⟩
    have h4 : |a + 2 * δ / 3| ≤ δ / 3 := by
      rw [abs_le] <;> constructor <;> linarith
    have h5 : (2 * ((0 : Fin 3) : ℝ) - 2) * δ / 3 = -2 * δ / 3 := by norm_num
    rw [h5]
    have h6 : a - (-2 * δ / 3) = a + 2 * δ / 3 := by ring
    rw [h6]
    exact h4
  · have h3' : a > -δ / 3 := by linarith
    by_cases h4 : a ≤ δ / 3
    · refine ⟨(1 : Fin 3), ?_⟩
      have h5 : |a| ≤ δ / 3 := by
        rw [abs_le] <;> constructor <;> linarith
      have h6 : (2 * ((1 : Fin 3) : ℝ) - 2) * δ / 3 = 0 := by norm_num
      rw [h6] <;> simpa using h5
    · refine ⟨(2 : Fin 3), ?_⟩
      have h7 : |a - 2 * δ / 3| ≤ δ / 3 := by
        rw [abs_le] <;> constructor <;> linarith
      have h8 : (2 * ((2 : Fin 3) : ℝ) - 2) * δ / 3 = 2 * δ / 3 := by norm_num
      rw [h8] <;> exact h7

/-- The set of 9 centers forming a 3×3 grid around `c` with spacing `2δ/3`. -/
noncomputable
def nineCenters (δ : ℝ) (c : EuclideanPlane) : Set EuclideanPlane :=
  Set.image (fun (p : Fin 3 × Fin 3) =>
    let e0 : EuclideanPlane := EuclideanSpace.single 0 1
    let e1 : EuclideanPlane := EuclideanSpace.single 1 1
    c + ((2 * (p.1 : ℝ) - 2) * δ / 3) • e0 + ((2 * (p.2 : ℝ) - 2) * δ / 3) • e1)
    Set.univ

lemma nineCenters_encard_le_nine (δ : ℝ) (c : EuclideanPlane) :
    (nineCenters δ c).encard ≤ 9 := by
  have h1 : (nineCenters δ c).encard ≤ (Set.univ : Set (Fin 3 × Fin 3)).encard :=
    Set.encard_image_le _ _
  have h2 : (Set.univ : Set (Fin 3 × Fin 3)).encard ≤ 9 := by
    have hfin : (Set.univ : Set (Fin 3 × Fin 3)).Finite := Set.toFinite _
    have h3 : (Set.univ : Set (Fin 3 × Fin 3)).encard = ↑(hfin.toFinset.card) := by exact Set.Finite.encard_eq_coe_toFinset_card hfin
    rw [h3] <;> simp [hfin] <;> decide
  exact le_trans h1 h2

/-- A closed ball of radius `δ` in the Euclidean plane can be covered by
9 closed balls of radius `δ/2`, using a 3×3 grid with spacing `2δ/3`. -/
lemma ball_covered_by_nine (δ : ℝ) (c : EuclideanPlane) (hδ : 0 ≤ δ) :
    IsCover (δ / 2).toNNReal (closedBall c δ) (nineCenters δ c) := by
  rw [isCover_iff_subset_iUnion_closedBall]
  intro z hz
  have h_dist : ‖z - c‖ ≤ δ := hz
  let w : EuclideanPlane := z - c
  have hwnorm : ‖w‖ ≤ δ := h_dist
  have h_coord0 : |w 0| ≤ ‖w‖ := PiLp.norm_apply_le w 0
  have h_coord1 : |w 1| ≤ ‖w‖ := PiLp.norm_apply_le w 1
  have h0 : |w 0| ≤ δ := by linarith
  have h1 : |w 1| ≤ δ := by linarith
  rcases round_to_grid hδ h0 with ⟨k0, hk0⟩
  rcases round_to_grid hδ h1 with ⟨k1, hk1⟩
  let e0 : EuclideanPlane := EuclideanSpace.single 0 1
  let e1 : EuclideanPlane := EuclideanSpace.single 1 1
  let a0 : ℝ := (2 * (k0 : ℝ) - 2) * δ / 3
  let a1 : ℝ := (2 * (k1 : ℝ) - 2) * δ / 3
  let d : EuclideanPlane := c + a0 • e0 + a1 • e1
  have hd_in : d ∈ nineCenters δ c := by
    have himg : d ∈ Set.image (fun (p : Fin 3 × Fin 3) =>
        let e0 : EuclideanPlane := EuclideanSpace.single 0 1
        let e1 : EuclideanPlane := EuclideanSpace.single 1 1
        c + ((2 * (p.1 : ℝ) - 2) * δ / 3) • e0 + ((2 * (p.2 : ℝ) - 2) * δ / 3) • e1) Set.univ := by
      exact ⟨(k0, k1), by trivial, by simp [d, e0, e1, a0, a1]⟩
    exact himg
  have h_est0 : |w 0 - a0| ≤ δ / 3 := by simpa [a0] using hk0
  have h_est1 : |w 1 - a1| ≤ δ / 3 := by simpa [a1] using hk1
  have h_cd0 : (d - c) 0 = a0 := by
    simp [d, e0, e1, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply] <;> aesop
  have h_cd1 : (d - c) 1 = a1 := by
    simp [d, e0, e1, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply] <;> aesop
  have h_dist2 : ‖z - d‖ ≤ δ / 2 := by
    let v : EuclideanPlane := w - (d - c)
    have hv0 : v 0 = w 0 - a0 := by simp [v, PiLp.sub_apply, h_cd0]
    have hv1 : v 1 = w 1 - a1 := by simp [v, PiLp.sub_apply, h_cd1]
    have h_norm2 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v, Fin.sum_univ_two]
    have h_sq : ‖v‖ ^ 2 ≤ (δ / 2) ^ 2 := by
      rw [h_norm2, hv0, hv1]
      have h3 : (w 0 - a0) ^ 2 ≤ (δ / 3) ^ 2 := by
        have h31 : |w 0 - a0| ≤ δ / 3 := h_est0
        have h32 : |w 0 - a0| ^ 2 ≤ (δ / 3) ^ 2 := by gcongr <;> positivity
        have h33 : |w 0 - a0| ^ 2 = (w 0 - a0) ^ 2 := by rw [sq_abs]
        rw [h33] at h32; exact h32
      have h4 : (w 1 - a1) ^ 2 ≤ (δ / 3) ^ 2 := by
        have h41 : |w 1 - a1| ≤ δ / 3 := h_est1
        have h42 : |w 1 - a1| ^ 2 ≤ (δ / 3) ^ 2 := by gcongr <;> positivity
        have h43 : |w 1 - a1| ^ 2 = (w 1 - a1) ^ 2 := by rw [sq_abs]
        rw [h43] at h42; exact h42
      have h5 : 2 * (δ / 3) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h7 : (2 / 9 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
        have h8 : 0 ≤ δ ^ 2 := by positivity
        calc
          2 * (δ / 3) ^ 2 = (2 / 9 : ℝ) * δ ^ 2 := by ring
          _ ≤ (1 / 4 : ℝ) * δ ^ 2 := by gcongr
          _ = (δ / 2) ^ 2 := by ring
      linarith
    have h5 : 0 ≤ ‖v‖ := by positivity
    have h6 : 0 ≤ δ / 2 := by positivity
    have h_eq : ‖z - d‖ = ‖v‖ := by
      have h9 : z - d = v := by simp [v, w, sub_sub_sub_cancel_left]
      rw [h9]
    rw [h_eq]
    nlinarith [sq_nonneg (‖v‖ - δ / 2)]
  have h_nonneg2 : 0 ≤ δ / 2 := by positivity
  have h_rad : (↑((δ / 2).toNNReal) : ℝ) = δ / 2 := by exact Real.coe_toNNReal (δ / 2) h_nonneg2
  have h_z_in : z ∈ closedBall d (δ / 2).toNNReal := by
    have h_dist' : dist z d ≤ ↑(δ / 2).toNNReal := by
      rw [dist_eq_norm, h_rad]
      exact h_dist2
    exact h_dist'
  exact Set.mem_iUnion₂.mpr ⟨d, hd_in, h_z_in⟩

/-- A doubling property for external covering numbers in the Euclidean plane:
covering at half the radius costs at most a factor of 9.

Proof: a δ-ball can be covered by 9 balls of radius δ/2 (3×3 grid). Given a
δ-cover C of A, replacing each center by its 9-grid gives a (δ/2)-cover D
with |D| ≤ 9|C|. The infimum is attained because `ℕ∞` is well-ordered. -/
lemma externalCoveringNumber_half_le_plane (A : Set EuclideanPlane) (δ : NNReal) :
    externalCoveringNumber (δ / 2) A ≤ 9 * externalCoveringNumber δ A := by
  by_cases h_top : externalCoveringNumber δ A = ⊤
  · rw [h_top] <;> simp
  · have hfin : ∃ (n : ℕ), externalCoveringNumber δ A = ↑n := by exact Option.ne_none_iff_exists'.mp h_top
    rcases hfin with ⟨n, hn⟩
    have h1 : (↑n : ℕ∞) < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_self n
    have h2 : ¬ (↑(n + 1) : ℕ∞) ≤ externalCoveringNumber δ A := by
      rw [hn]; exact not_le.mpr h1
    have h3 : ∃ (C : Set EuclideanPlane), IsCover δ A C ∧ ¬ (↑(n + 1) : ℕ∞) ≤ C.encard := by
      simpa [externalCoveringNumber, le_iInf_iff] using h2
    rcases h3 with ⟨C, hC, hlt⟩
    have h4 : C.encard < ↑(n + 1) := by exact Std.not_le.mp hlt
    have h5 : externalCoveringNumber δ A ≤ C.encard := IsCover.externalCoveringNumber_le_encard hC
    have h6 : (↑n : ℕ∞) ≤ C.encard := by rw [hn] at h5; exact h5
    have h7 : C.encard = ↑n := by
      have h_ne_top : C.encard ≠ ⊤ := by
        intro h_top2; rw [h_top2] at h4; simp at h4
      have h_exists : ∃ (m : ℕ), C.encard = ↑m := by exact Option.ne_none_iff_exists'.mp h_ne_top
      rcases h_exists with ⟨m, hm⟩
      rw [hm] at h6 h4
      have hmn : n ≤ m := by exact_mod_cast h6
      have hmn2 : m < n + 1 := by exact_mod_cast h4
      have hmeq : m = n := by omega
      rw [hmeq] at hm; exact hm
    let D : Set EuclideanPlane := {d | ∃ c ∈ C, d ∈ nineCenters (δ : ℝ) c}
    have hD_cover : IsCover (δ / 2) A D := by
      rw [isCover_iff_subset_iUnion_closedBall]
      intro z hz
      have hU : A ⊆ ⋃ c ∈ C, closedBall c (δ : ℝ) :=
        (isCover_iff_subset_iUnion_closedBall.mp hC)
      rcases Set.mem_iUnion₂.mp (hU hz) with ⟨c, hcC, hzc⟩
      have h_rad_eq : ((↑δ / 2 : ℝ).toNNReal) = δ / 2 := by ext <;> simp <;> positivity
      have h9 : IsCover (δ / 2) (closedBall c (δ : ℝ)) (nineCenters (δ : ℝ) c) := by
        rw [← h_rad_eq]; exact ball_covered_by_nine (δ : ℝ) c (by positivity)
      have h10 : closedBall c (δ : ℝ) ⊆ ⋃ d ∈ nineCenters (δ : ℝ) c, closedBall d (δ / 2) :=
        (isCover_iff_subset_iUnion_closedBall.mp h9)
      rcases Set.mem_iUnion₂.mp (h10 hzc) with ⟨d, hd_in, hdz⟩
      have hD_in : d ∈ D := ⟨c, hcC, hd_in⟩
      exact Set.mem_iUnion₂.mpr ⟨d, hD_in, hdz⟩
    let f : EuclideanPlane × (Fin 3 × Fin 3) → EuclideanPlane := fun p =>
      let e0 : EuclideanPlane := EuclideanSpace.single 0 1
      let e1 : EuclideanPlane := EuclideanSpace.single 1 1
      p.1 + ((2 * (p.2.1 : ℝ) - 2) * (δ : ℝ) / 3) • e0
          + ((2 * (p.2.2 : ℝ) - 2) * (δ : ℝ) / 3) • e1
    have hD_subset : D ⊆ Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))) := by
      intro d hd
      rcases hd with ⟨c, hcC, hdnine⟩
      have h_exists : ∃ (p : Fin 3 × Fin 3), p ∈ (Set.univ : Set (Fin 3 × Fin 3)) ∧ f (c, p) = d := by
        simpa [nineCenters, f] using hdnine
      rcases h_exists with ⟨p, hp, rfl⟩
      exact Set.mem_image_of_mem f ⟨hcC, hp⟩
    have hD_encard : D.encard ≤ 9 * C.encard := by
      have h1 : D.encard ≤ (Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3)))).encard :=
        Set.encard_mono hD_subset
      have h2 : (Set.image f (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3)))).encard ≤
                  (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard := Set.encard_image_le _ _
      have h3 : (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard =
                  C.encard * (Set.univ : Set (Fin 3 × Fin 3)).encard := Set.encard_prod
      have h4 : (Set.univ : Set (Fin 3 × Fin 3)).encard ≤ 9 := by
        have hfin : (Set.univ : Set (Fin 3 × Fin 3)).Finite := Set.toFinite _
        have h5 : (Set.univ : Set (Fin 3 × Fin 3)).encard = ↑(hfin.toFinset.card) := by exact Set.Finite.encard_eq_coe_toFinset_card hfin
        rw [h5] <;> simp [hfin] <;> decide
      calc
        D.encard ≤ (Set.image f (C ×ˢ Set.univ)).encard := h1
        _ ≤ (C ×ˢ (Set.univ : Set (Fin 3 × Fin 3))).encard := h2
        _ = C.encard * (Set.univ : Set (Fin 3 × Fin 3)).encard := h3
        _ ≤ C.encard * 9 := by gcongr
        _ = 9 * C.encard := by ring
    have h_main : externalCoveringNumber (δ / 2) A ≤ D.encard :=
      IsCover.externalCoveringNumber_le_encard hD_cover
    have h_final : D.encard ≤ 9 * externalCoveringNumber δ A := by
      have h10 : 9 * C.encard = 9 * externalCoveringNumber δ A := by
        calc 9 * C.encard = 9 * (↑n : ℕ∞) := by rw [h7]
             _ = 9 * externalCoveringNumber δ A := by rw [hn]
      rw [h10] at hD_encard
      exact hD_encard
    exact le_trans h_main h_final

/-- Given a `(δ, s, C)`-set `P` in the Euclidean plane, there exists a
probability measure `μ` supported on `P` such that
`μ (closedBall x r) ≤ C' * r^s` for all `x` and `r ≥ δ`.

This is the discretized Frostman lemma. The proof uses a maximal `δ`-separated
subset and the doubling property of covering numbers in `ℝ²`.

The continuous Frostman lemma from the upstream mathlib extension (`frostman_forward`) applies
when the set has positive Hausdorff measure; here we use the covering-number
characterization directly. -/
theorem IsDeltaSSet.frostmanMeasure {δ s C : ℝ} {P : Set EuclideanPlane}
    (h : IsDeltaSSet δ s C P) (hP_bounded : Bornology.IsBounded P) :
    ∃ (μ : Measure EuclideanPlane) (S : Finset EuclideanPlane),
      μ Set.univ = 1 ∧
      μ Pᶜ = 0 ∧
      (μ = (S.card : ENNReal)⁻¹ • Measure.count.restrict (S : Set EuclideanPlane)) ∧
      S.Nonempty ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ ‖p - q‖) ∧
      (∀ p ∈ S, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ s * S.card) ∧
      (∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
        μ (closedBall x r) ≤ ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s)) := by
  have hδpos : 0 < δ := h.2.1
  have hCpos : 0 < C := h.2.2.1
  have hs_nonneg : 0 ≤ s := h.2.2.2.1
  have hPnonempty : P.Nonempty := h.1
  let δ' : NNReal := ⟨δ, hδpos.le⟩
  have hδ'_co : (δ' : ℝ) = δ := by rfl
  have hδ'pos : 0 < δ' := by exact_mod_cast hδpos
  have hP_tb : TotallyBounded P := by
    rcases hP_bounded.subset_closedBall (0 : EuclideanPlane) with ⟨R, hR⟩
    have hK : IsCompact (Metric.closedBall (0 : EuclideanPlane) R) :=
      isCompact_closedBall (0 : EuclideanPlane) R
    have hTB : TotallyBounded (Metric.closedBall (0 : EuclideanPlane) R) :=
      hK.totallyBounded
    exact hTB.subset hR
  have h_ec_ne_top : externalCoveringNumber (δ' / 2) P ≠ ⊤ := by
    have hhalf_pos : 0 < δ' / 2 := by positivity
    have hfc := exists_finite_isCover_of_totallyBounded hhalf_pos.ne' hP_tb
    rcases hfc with ⟨N, _, hNfin, hNcover⟩
    have h : externalCoveringNumber (δ' / 2) P ≤ N.encard :=
      IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact Set.encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hmul : 2 * (δ' / 2) = δ' := by
    apply NNReal.coe_injective
    simp [hδ'_co] <;> ring
  have h_pack_ne_top : packingNumber δ' P ≠ ⊤ := by
    have h : packingNumber (2 * (δ' / 2)) P ≤ externalCoveringNumber (δ' / 2) P :=
      packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) P
    rw [hmul] at h
    exact ne_top_of_le_ne_top h_ec_ne_top h
  let S : Set EuclideanPlane := maximalSeparatedSet δ' P
  have hS_subset : S ⊆ P := maximalSeparatedSet_subset
  have hS_sep : IsSeparated δ' S := isSeparated_maximalSeparatedSet
  have hS_encard : S.encard = packingNumber δ' P := encard_maximalSeparatedSet h_pack_ne_top
  have hS_cover : IsCover δ' P S := isCover_maximalSeparatedSet h_pack_ne_top
  have hS_finite : S.Finite := by
    have h : S.encard ≠ ⊤ := by rw [hS_encard] <;> exact h_pack_ne_top
    exact Set.encard_ne_top_iff.mp h
  have hS_nonempty : S.Nonempty := hS_cover.nonempty hPnonempty
  have hS_encard_pos : 0 < S.encard := by
    have h : 0 < packingNumber δ' P := packingNumber_pos_iff.mpr hPnonempty
    rw [hS_encard] <;> exact h
  classical
  let Sfin : Finset EuclideanPlane := hS_finite.toFinset
  have hSfin_eq : (Sfin : Set EuclideanPlane) = S := by simp [Sfin]
  have hSfin_card : S.encard = ↑Sfin.card := by rw [← hSfin_eq] <;> simp
  have hSfin_pos : 0 < Sfin.card := by
    have h : 0 < S.encard := hS_encard_pos
    rw [hSfin_card] at h
    exact_mod_cast h
  let μ : Measure EuclideanPlane := (↑Sfin.card : ENNReal)⁻¹ • Measure.count.restrict S
  have hμ_univ : μ Set.univ = 1 := by
    have h1 : μ Set.univ = (↑Sfin.card : ENNReal)⁻¹ * Measure.count.restrict S Set.univ := by rfl
    rw [h1]
    have hS_meas : MeasurableSet S := hS_finite.measurableSet
    have h2 : Measure.count.restrict S Set.univ = S.encard := by
      have h21 : Measure.count.restrict S Set.univ = Measure.count (Set.univ ∩ S) :=
        Measure.restrict_apply MeasurableSet.univ
      rw [h21]
      have h22 : Set.univ ∩ S = S := by simp
      rw [h22]
      exact Measure.count_apply hS_meas
    rw [h2, hSfin_card]
    have h3 : (↑Sfin.card : ENNReal) ≠ 0 := by exact_mod_cast hSfin_pos.ne'
    have h4 : (↑Sfin.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Sfin.card
    have h5 : (↑Sfin.card : ENNReal)⁻¹ * ↑Sfin.card = 1 := by
      exact ENNReal.inv_mul_cancel h3 h4
    exact h5
  have hS_meas : MeasurableSet S := hS_finite.measurableSet
  have hμ_compl : μ Pᶜ = 0 := by
    have h1 : S ∩ Pᶜ = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hx.2 (hS_subset hx.1)
    have h2 : Measure.count.restrict S Pᶜ = 0 := by
      have h1' : Pᶜ ⊆ Sᶜ := by
        intro x hx
        simp only [Set.mem_compl_iff] at hx ⊢
        intro hSx
        exact hx (hS_subset hSx)
      have h3 : Measure.count.restrict S Pᶜ ≤ Measure.count.restrict S Sᶜ := measure_mono h1'
      have h4 : Measure.count.restrict S Sᶜ = 0 := by
        have h41 : Measure.count.restrict S Sᶜ = Measure.count (Sᶜ ∩ S) :=
          Measure.restrict_apply hS_meas.compl
        rw [h41]
        have h42 : Sᶜ ∩ S = ∅ := by simp
        rw [h42] <;> simp
      have h5 : Measure.count.restrict S Pᶜ ≤ 0 := by
        rw [h4] at h3
        exact h3
      exact le_antisymm h5 (by positivity)
    have h3 : μ Pᶜ = (↑Sfin.card : ENNReal)⁻¹ * Measure.count.restrict S Pᶜ := by rfl
    rw [h3, h2] <;> simp
  have h_main : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      μ (closedBall x r) ≤ ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) := by
    intro x r hr
    have hrpos : 0 < r := by linarith
    have hrnonneg : 0 ≤ r := by linarith
    let B : Set EuclideanPlane := closedBall x r
    have hSB_subset : S ∩ B ⊆ P ∩ B := by
      intro y hy
      exact ⟨hS_subset hy.1, hy.2⟩
    have hSB_subset_S : S ∩ B ⊆ S := by intro y hy; exact hy.1
    have hSB_sep : IsSeparated δ' (S ∩ B) := IsSeparated.subset hSB_subset_S hS_sep
    have hSB_finite : (S ∩ B).Finite := by exact Set.Finite.inter_of_left hS_finite B
    let S'B : Finset EuclideanPlane := hSB_finite.toFinset
    have hS'B_eq : (S'B : Set EuclideanPlane) = S ∩ B := by simp [S'B]
    have h1 : (S ∩ B).encard ≤ packingNumber δ' (P ∩ B) :=
      IsSeparated.encard_le_packingNumber hSB_subset hSB_sep
    have h2 : packingNumber δ' (P ∩ B) ≤ externalCoveringNumber (δ' / 2) (P ∩ B) := by
      have h2' : packingNumber (2 * (δ' / 2)) (P ∩ B) ≤
          externalCoveringNumber (δ' / 2) (P ∩ B) :=
        packingNumber_two_mul_le_externalCoveringNumber (δ' / 2) (P ∩ B)
      rw [hmul] at h2'
      exact h2'
    have h3 : externalCoveringNumber (δ' / 2) (P ∩ B) ≤ 9 * externalCoveringNumber δ' (P ∩ B) :=
      externalCoveringNumber_half_le_plane (P ∩ B) δ'
    have hδ'_eq : δ' = δ.toNNReal := by
      ext <;> simp [δ', hδ'_co] <;> linarith
    have h4 : (externalCoveringNumber δ' (P ∩ B) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (externalCoveringNumber δ' P : ENNReal) := by
      have h5 := h.2.2.2.2 x r hr
      rw [hδ'_eq] at *
      exact h5
    have h5 : externalCoveringNumber δ' P ≤ S.encard :=
      IsCover.externalCoveringNumber_le_encard hS_cover
    have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hrnonneg hs_nonneg]
    have h9C : (9 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal (9 * C) := by
      have h11 : 0 ≤ C := by linarith
      have h12 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
        simp [ENNReal.ofReal_mul h11] <;> norm_num
      exact h12.symm
    have h6 : (↑S'B.card : ENNReal) ≤
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * (↑Sfin.card : ENNReal) := by
      have h1_eq : (S ∩ B).encard = ↑S'B.card := by
        have h : (S'B : Set EuclideanPlane) = S ∩ B := hS'B_eq
        rw [← h]
        simp
      have h1' : (↑S'B.card : ENNReal) ≤ ↑(packingNumber δ' (P ∩ B)) := by
        have h1'' : (↑S'B.card : ℕ∞) ≤ packingNumber δ' (P ∩ B) := by
          rw [← h1_eq]
          exact h1
        exact_mod_cast h1''
      have h2' : (↑(packingNumber δ' (P ∩ B)) : ENNReal) ≤
          (↑(externalCoveringNumber (δ' / 2) (P ∩ B)) : ENNReal) := by
        exact_mod_cast h2
      have h3' : ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) ≤
          (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := by exact_mod_cast h3
      have h4' : (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (↑Sfin.card : ENNReal) := by
        calc
          (↑(externalCoveringNumber δ' (P ∩ B)) : ENNReal)
            ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (↑(externalCoveringNumber δ' P) : ENNReal) := h4
          _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (↑Sfin.card : ENNReal) := by
            gcongr
            have h61 : (↑(externalCoveringNumber δ' P) : ENNReal) ≤ (↑Sfin.card : ENNReal) := by
              exact_mod_cast (le_trans h5 (le_of_eq hSfin_card))
            exact h61
      calc
        (↑S'B.card : ENNReal)
          ≤ ↑(packingNumber δ' (P ∩ B)) := h1'
        _ ≤ ↑(externalCoveringNumber (δ' / 2) (P ∩ B)) := h2'
        _ ≤ (9 : ENNReal) * ↑(externalCoveringNumber δ' (P ∩ B)) := h3'
        _ ≤ (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (↑Sfin.card : ENNReal)) := by
          gcongr <;> exact h4'
        _ = ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * (↑Sfin.card : ENNReal) := by
          have h_assoc : (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ↑Sfin.card) =
              ((9 : ENNReal) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ s * ↑Sfin.card := by
            simp [mul_assoc]
          rw [h_assoc, h9C, h_rpow]
          <;> simp [mul_assoc]
    have hμB : μ B = (↑Sfin.card : ENNReal)⁻¹ * ↑S'B.card := by
      have h1 : μ B = (↑Sfin.card : ENNReal)⁻¹ * Measure.count.restrict S B := by rfl
      rw [h1]
      have hB_meas : MeasurableSet B := isClosed_closedBall.measurableSet
      have h2 : Measure.count.restrict S B = (S ∩ B).encard := by
        rw [Measure.restrict_apply hB_meas]
        have h_comm : B ∩ S = S ∩ B := by ext x; simp [and_comm]
        rw [h_comm]
        exact Measure.count_apply hSB_finite.measurableSet
      have h_eq2 : (S ∩ B).encard = ↑S'B.card := by
        have h : (S'B : Set EuclideanPlane) = S ∩ B := hS'B_eq
        rw [← h]
        simp
      rw [h2, h_eq2]
      <;> norm_cast
    rw [hμB]
    have h10 : (↑Sfin.card : ENNReal) ≠ 0 := by exact_mod_cast hSfin_pos.ne'
    have h11 : (↑Sfin.card : ENNReal) ≠ ⊤ := by exact_mod_cast (by simp)
    calc
      (↑Sfin.card : ENNReal)⁻¹ * ↑S'B.card
        ≤ (↑Sfin.card : ENNReal)⁻¹ * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * (↑Sfin.card : ENNReal)) := by gcongr
      _ = ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) := by
        have h12 : (↑Sfin.card : ENNReal)⁻¹ * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * (↑Sfin.card : ENNReal))
            = ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * ((↑Sfin.card : ENNReal)⁻¹ * (↑Sfin.card : ENNReal)) := by
          simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
        rw [h12]
        have h13 : (↑Sfin.card : ENNReal)⁻¹ * (↑Sfin.card : ENNReal) = 1 := by
          exact ENNReal.inv_mul_cancel h10 h11
        rw [h13] <;> ring
  have hS_sep' : ∀ p ∈ Sfin, ∀ q ∈ Sfin, p ≠ q → δ ≤ ‖p - q‖ := by
    intro p hp q hq hne
    have hpS : p ∈ S := by rw [← hSfin_eq]; exact hp
    have hqS : q ∈ S := by rw [← hSfin_eq]; exact hq
    have h4 : (δ' : ENNReal) < edist p q := hS_sep hpS hqS hne
    have h_edist : edist p q = ENNReal.ofReal (dist p q) := by exact edist_dist p q
    have h_coe : (δ' : ENNReal) = ENNReal.ofReal (δ' : ℝ) := by exact ENNReal.coe_nnreal_eq δ'
    rw [h_edist, h_coe] at h4
    have h4' : (δ' : ℝ) < dist p q := by
      by_contra h
      have h' : dist p q ≤ (δ' : ℝ) := by linarith
      have h_contra : ENNReal.ofReal (dist p q) ≤ ENNReal.ofReal (δ' : ℝ) :=
        ENNReal.ofReal_le_ofReal h'
      exact not_le.mpr h4 h_contra
    have h4'' : (δ' : ℝ) ≤ dist p q := by linarith
    have h5 : (δ' : ℝ) = δ := hδ'_co
    have h6 : dist p q = ‖p - q‖ := by rw [dist_eq_norm]
    rw [h5, h6] at h4''
    exact h4''
  have hS_ball' : ∀ p ∈ Sfin, ∀ r : ℝ, δ ≤ r →
      (Sfin.filter (fun q => ‖p - q‖ ≤ r)).card ≤ (9 * C) * r ^ s * Sfin.card := by
    intro p hp r hr
    let B : Set EuclideanPlane := closedBall p r
    have hB_meas : MeasurableSet B := isClosed_closedBall.measurableSet
    have hSB_finite : (S ∩ B).Finite := by exact Set.Finite.inter_of_left hS_finite B
    let S'B : Finset EuclideanPlane := hSB_finite.toFinset
    have hS'B_eq : (S'B : Set EuclideanPlane) = S ∩ B := by simp [S'B]
    have h_filter_eq : Sfin.filter (fun q => ‖p - q‖ ≤ r) = S'B := by
      ext q
      have h1 : q ∈ Sfin.filter (fun q => ‖p - q‖ ≤ r) ↔ q ∈ Sfin ∧ ‖p - q‖ ≤ r := by
        simp
      have h2 : q ∈ S'B ↔ q ∈ S ∧ q ∈ B := by
        simp [S'B, Set.Finite.mem_toFinset]
        <;> rfl
      rw [h1, h2]
      have h3 : q ∈ Sfin ↔ q ∈ S := by
        change q ∈ (Sfin : Set EuclideanPlane) ↔ q ∈ S
        rw [hSfin_eq]
      have h4 : q ∈ B ↔ ‖p - q‖ ≤ r := by
        have h41 : q ∈ B ↔ dist q p ≤ r := by
          dsimp only [B]
          simp [Metric.mem_closedBall]
          <;> rfl
        have h42 : dist q p = dist p q := dist_comm q p
        have h43 : dist p q = ‖p - q‖ := by rw [dist_eq_norm]
        rw [h41, h42, h43]
      rw [h3, h4]
    have h1 : μ B ≤ ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) := h_main p r hr
    have hr_pos : 0 < r := by linarith
    have hμB : μ B = (↑Sfin.card : ENNReal)⁻¹ * ↑S'B.card := by
      have h2 : Measure.count.restrict S B = (S ∩ B).encard := by
        rw [Measure.restrict_apply hB_meas]
        have h_comm : B ∩ S = S ∩ B := by ext x; simp [and_comm]
        rw [h_comm]
        exact Measure.count_apply hSB_finite.measurableSet
      have h_eq2 : (S ∩ B).encard = ↑S'B.card := by
        rw [← hS'B_eq]; simp
      have h3 : μ B = (↑Sfin.card : ENNReal)⁻¹ * Measure.count.restrict S B := by rfl
      rw [h3, h2]
      have h4 : ((S ∩ B).encard : ENNReal) = (↑S'B.card : ENNReal) := by
        exact_mod_cast h_eq2
      rw [h4]
    rw [hμB] at h1
    have h10 : (↑Sfin.card : ENNReal) ≠ 0 := by exact_mod_cast hSfin_pos.ne'
    have h11 : (↑Sfin.card : ENNReal) ≠ ⊤ := by exact_mod_cast (by simp)
    have h14 : ↑S'B.card ≤ (↑Sfin.card : ENNReal) * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s)) := by
      calc
        ↑S'B.card
          = (↑Sfin.card : ENNReal) * ((↑Sfin.card : ENNReal)⁻¹ * ↑S'B.card) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel h10 h11] <;> ring
        _ ≤ (↑Sfin.card : ENNReal) * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s)) := by gcongr
    have h16 : 0 ≤ (9 * C) * r ^ s := by
      have h161 : 0 ≤ 9 * C := by linarith
      have h162 : 0 ≤ r ^ s := Real.rpow_nonneg hr_pos.le s
      exact mul_nonneg h161 h162
    have h15 : (↑Sfin.card : ENNReal) * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s)) =
        ENNReal.ofReal ((9 * C) * r ^ s * (Sfin.card : ℝ)) := by
      have h181 : 0 ≤ 9 * C := by linarith
      have h18 : ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) = ENNReal.ofReal ((9 * C) * r ^ s) := by
        exact (ENNReal.ofReal_mul h181).symm
      have h19 : (↑Sfin.card : ENNReal) = ENNReal.ofReal (Sfin.card : ℝ) := by simp
      have h20 : 0 ≤ (Sfin.card : ℝ) := by positivity
      calc
        (↑Sfin.card : ENNReal) * (ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s))
          = ENNReal.ofReal (Sfin.card : ℝ) * ENNReal.ofReal ((9 * C) * r ^ s) := by rw [h18, h19]
        _ = ENNReal.ofReal ((Sfin.card : ℝ) * ((9 * C) * r ^ s)) := by
          rw [← ENNReal.ofReal_mul h20]
        _ = ENNReal.ofReal ((9 * C) * r ^ s * (Sfin.card : ℝ)) := by
          congr 1; ring
    let F := Sfin.filter (fun q => ‖p - q‖ ≤ r)
    have hF_eq : F = S'B := h_filter_eq
    have h14' : (↑F.card : ENNReal) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (Sfin.card : ℝ)) := by
      have h_eq_F : (↑F.card : ENNReal) = ↑S'B.card := by rw [hF_eq]
      rw [h_eq_F]
      rw [h15] at h14
      exact h14
    have h_eq : (↑F.card : ENNReal) = ENNReal.ofReal (F.card : ℝ) := by
      exact_mod_cast rfl
    have h14'' : ENNReal.ofReal (F.card : ℝ) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (Sfin.card : ℝ)) := by
      rw [←h_eq]
      exact h14'
    have h_nonneg : 0 ≤ (9 * C) * r ^ s * (Sfin.card : ℝ) := by
      have h1 : 0 ≤ 9 * C := by linarith
      have h2 : 0 ≤ r ^ s := Real.rpow_nonneg hr_pos.le s
      have h3 : 0 ≤ (Sfin.card : ℝ) := Nat.cast_nonneg Sfin.card
      exact mul_nonneg (mul_nonneg h1 h2) h3
    have h17 : (F.card : ℝ) ≤ (9 * C) * r ^ s * (Sfin.card : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h14''
    simpa [F] using h17
  have hμ_eq : μ = (Sfin.card : ENNReal)⁻¹ • Measure.count.restrict (Sfin : Set EuclideanPlane) := by
    have h : (Sfin : Set EuclideanPlane) = S := hSfin_eq
    simp [μ, h]
  have hSfin_nonempty : Sfin.Nonempty := by
    obtain ⟨x, hx⟩ := hS_nonempty
    have hx' : x ∈ (Sfin : Set EuclideanPlane) := by
      rw [hSfin_eq]
      exact hx
    exact ⟨x, by simpa using hx'⟩
  exact ⟨μ, Sfin, hμ_univ, hμ_compl, hμ_eq, hSfin_nonempty, hS_sep', hS_ball', h_main⟩
