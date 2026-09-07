module

/-
  S-set transfer through affine map + grid snapping.

  Given a (Δ, s, C)-set T in EuclideanPlane, the snapped affine image
  (scale by Δ, translate, snap to δ-grid) satisfies IsRescalableDeltaSet
  with constant 625 * (1 + 1/√2)^s * C.

  Key steps:
  1. Unsnapped scaled image satisfies IsRescalableDeltaSet with same constant C
     (via externalCoveringNumber_smul and translation invariance).
  2. Snapping perturbs each point by ≤ δ/√2, which degrades covering numbers
     by at most a factor of 25 in each direction (2D grid doubling).
  3. Intersection with a ball shifts the radius by at most δ/√2, which is
     absorbed since r ≥ Δ and δ = Δ².

  Whiteprint node: construct_fine_params / sset_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.CoveringScaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Ratio `1 + 1/√2`: snapping perturbation + covering radius. -/
def snapCoverRatio : ℝ := 1 + 1 / Real.sqrt 2

lemma snapCoverRatio_pos : 0 < snapCoverRatio := by
  have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  dsimp only [snapCoverRatio]
  have h2 : 0 < 1 / Real.sqrt 2 := by positivity
  linarith

lemma snapCoverRatio_lt_two : snapCoverRatio < 2 := by
  have h1 : 1 < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 : 1 / Real.sqrt 2 < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  dsimp only [snapCoverRatio]
  linarith

/-- Nearest-integer rounding: |z - floor(z + 1/2)| ≤ 1/2. -/
lemma round_half_near (z : ℝ) : |z - (Int.floor (z + 1 / 2) : ℝ)| ≤ 1 / 2 := by
  let i : ℤ := Int.floor (z + 1 / 2)
  have h1 : (i : ℝ) ≤ z + 1 / 2 := Int.floor_le _
  have h2 : z + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : -(1 / 2 : ℝ) ≤ z - (i : ℝ) := by linarith
  have h4 : z - (i : ℝ) ≤ 1 / 2 := by linarith
  exact abs_le.mpr ⟨h3, h4⟩

/-- If |z| < 2, then floor(z + 1/2) ∈ {-2, -1, 0, 1, 2}. -/
lemma round_in_Icc2 (z : ℝ) (h : |z| < 2) :
    Int.floor (z + 1 / 2) ∈ Finset.Icc (-2 : ℤ) 2 := by
  let i : ℤ := Int.floor (z + 1 / 2)
  have h1 : -2 < z := by linarith [abs_lt.mp h]
  have h2 : z < 2 := by linarith [abs_lt.mp h]
  have h3 : (i : ℝ) ≤ z + 1 / 2 := Int.floor_le _
  have h4 : z + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have h5 : -2 ≤ i := by
    have h6 : (i : ℝ) > -5 / 2 := by linarith
    by_contra h7
    have h8 : i ≤ -3 := by linarith
    have h9 : (i : ℝ) ≤ -3 := by exact_mod_cast h8
    linarith
  have h8 : i ≤ 2 := by
    have h9 : (i : ℝ) < 5 / 2 := by linarith
    by_contra h10
    have h11 : i ≥ 3 := by linarith
    have h12 : (i : ℝ) ≥ 3 := by exact_mod_cast h11
    linarith
  simp only [Finset.mem_Icc] <;> exact ⟨h5, h8⟩

/-- Coordinate absolute value bounded by Euclidean norm. -/
lemma coord_abs_le_norm (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  have h1 : ‖z‖ ^ 2 = ∑ j : Fin 2, ‖z j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
  have h2 : ‖z i‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h1]
    have h3 : ‖z i‖ ^ 2 ≤ ∑ j : Fin 2, ‖z j‖ ^ 2 := by
      apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    exact h3
  have h4 : |z i| = ‖z i‖ := by
    exact Real.ext_cauchy rfl
  have h5 : 0 ≤ |z i| := by positivity
  have h6 : 0 ≤ ‖z‖ := by positivity
  rw [h4] at *
  nlinarith

/-- A closed ball of radius `snapCoverRatio * ε` is covered by 25 closed balls of radius ε. -/
lemma ball_covered_by_25 {ε : ℝ} (hε : 0 < ε) (x : Plane) :
    ∃ (S : Finset Plane), S.card = 25 ∧
      Metric.closedBall x (snapCoverRatio * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε := by
  let I : Finset ℤ := Finset.Icc (-2) 2
  let disp : ℤ × ℤ → Plane := fun p =>
    WithLp.toLp (2 : ENNReal) (fun i : Fin 2 =>
      if i = 0 then (p.1 : ℝ) * ε else (p.2 : ℝ) * ε)
  let gridPoint : ℤ × ℤ → Plane := fun p => x + disp p
  let S : Finset Plane := (I ×ˢ I).image gridPoint
  refine ⟨S, ?_, ?_⟩
  · have h_inj : Function.Injective gridPoint := by
      intro p q h
      have h0 : (gridPoint p) 0 = (gridPoint q) 0 := by rw [h]
      have h1 : (p.1 : ℝ) = (q.1 : ℝ) := by
        have h_disj : (p.1 : ℝ) = (q.1 : ℝ) ∨ ε = 0 := by
          simpa [gridPoint, disp] using h0
        exact h_disj.resolve_right hε.ne'
      have h2' : (gridPoint p) 1 = (gridPoint q) 1 := by rw [h]
      have h2 : (p.2 : ℝ) = (q.2 : ℝ) := by
        have h_disj : (p.2 : ℝ) = (q.2 : ℝ) ∨ ε = 0 := by
          simpa [gridPoint, disp] using h2'
        exact h_disj.resolve_right hε.ne'
      exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_product]
    <;> simp [I] <;> decide
  · intro y hy
    have hdist : dist y x ≤ snapCoverRatio * ε := by simpa [Metric.mem_closedBall] using hy
    have hnorm : ‖y - x‖ ≤ snapCoverRatio * ε := by simpa [dist_eq_norm] using hdist
    have hc0 : |(y - x) 0| ≤ snapCoverRatio * ε := by
      calc |(y - x) 0| ≤ ‖y - x‖ := coord_abs_le_norm (y - x) 0
        _ ≤ _ := hnorm
    have hc1 : |(y - x) 1| ≤ snapCoverRatio * ε := by
      calc |(y - x) 1| ≤ ‖y - x‖ := coord_abs_le_norm (y - x) 1
        _ ≤ _ := hnorm
    have hdiv0 : |(y - x) 0| / ε ≤ snapCoverRatio := by
      calc |(y - x) 0| / ε
        ≤ (snapCoverRatio * ε) / ε := by gcongr
      _ = snapCoverRatio := by
        field_simp [hε.ne'] <;> ring
    have hlt0 : |(y - x) 0 / ε| < 2 := by
      have h : |(y - x) 0 / ε| = |(y - x) 0| / ε := by
        rw [abs_div]
        <;> rw [abs_of_pos hε]
      rw [h]
      have h3 : snapCoverRatio < 2 := snapCoverRatio_lt_two
      linarith
    have hdiv1 : |(y - x) 1| / ε ≤ snapCoverRatio := by
      calc |(y - x) 1| / ε
        ≤ (snapCoverRatio * ε) / ε := by gcongr
      _ = snapCoverRatio := by
        field_simp [hε.ne'] <;> ring
    have hlt1 : |(y - x) 1 / ε| < 2 := by
      have h : |(y - x) 1 / ε| = |(y - x) 1| / ε := by
        rw [abs_div]
        <;> rw [abs_of_pos hε]
      rw [h]
      have h3 : snapCoverRatio < 2 := snapCoverRatio_lt_two
      linarith
    let i : ℤ := Int.floor ((y - x) 0 / ε + 1 / 2)
    let j : ℤ := Int.floor ((y - x) 1 / ε + 1 / 2)
    have hi_round : |(y - x) 0 / ε - (i : ℝ)| ≤ 1 / 2 := round_half_near ((y - x) 0 / ε)
    have hj_round : |(y - x) 1 / ε - (j : ℝ)| ≤ 1 / 2 := round_half_near ((y - x) 1 / ε)
    have hi_I : i ∈ I := round_in_Icc2 ((y - x) 0 / ε) hlt0
    have hj_I : j ∈ I := round_in_Icc2 ((y - x) 1 / ε) hlt1
    let g : Plane := gridPoint (i, j)
    have hgS : g ∈ S := by
      apply Finset.mem_image.mpr
      exact ⟨(i, j), by simp [hi_I, hj_I], rfl⟩
    have hg0 : (gridPoint (i, j)) 0 = x 0 + (i : ℝ) * ε := by
      simp [gridPoint, disp, Pi.add_apply]
      <;> ring
    have hg1 : (gridPoint (i, j)) 1 = x 1 + (j : ℝ) * ε := by
      simp [gridPoint, disp, Pi.add_apply]
      <;> ring
    have hdx : |(y - g) 0| ≤ ε / 2 := by
      have h_coord : g 0 = x 0 + (i : ℝ) * ε := by
        have h_eq : g = gridPoint (i, j) := by rfl
        rw [h_eq]
        exact hg0
      have h : (y - g) 0 = (y - x) 0 - (i : ℝ) * ε := by
        have h9 : (y - g) 0 = y 0 - g 0 := by simp [Pi.sub_apply]
        rw [h9, h_coord]
        <;> simp [Pi.sub_apply] <;> ring
      rw [h]
      have h51 : (y - x) 0 - (i : ℝ) * ε = ε * ((y - x) 0 / ε - (i : ℝ)) := by
        field_simp [hε.ne'] <;> ring
      have h5 : |(y - x) 0 - (i : ℝ) * ε| = ε * |(y - x) 0 / ε - (i : ℝ)| := by
        rw [h51, abs_mul, abs_of_pos hε]
      rw [h5]
      have h6 : ε * |(y - x) 0 / ε - (i : ℝ)| ≤ ε * (1 / 2) := by
        gcongr
        <;> exact hi_round
      linarith
    have hdy : |(y - g) 1| ≤ ε / 2 := by
      have h_coord : g 1 = x 1 + (j : ℝ) * ε := by
        have h_eq : g = gridPoint (i, j) := by rfl
        rw [h_eq]
        exact hg1
      have h : (y - g) 1 = (y - x) 1 - (j : ℝ) * ε := by
        have h9 : (y - g) 1 = y 1 - g 1 := by simp [Pi.sub_apply]
        rw [h9, h_coord]
        <;> simp [Pi.sub_apply] <;> ring
      rw [h]
      have h51 : (y - x) 1 - (j : ℝ) * ε = ε * ((y - x) 1 / ε - (j : ℝ)) := by
        field_simp [hε.ne'] <;> ring
      have h5 : |(y - x) 1 - (j : ℝ) * ε| = ε * |(y - x) 1 / ε - (j : ℝ)| := by
        rw [h51, abs_mul, abs_of_pos hε]
      rw [h5]
      have h6 : ε * |(y - x) 1 / ε - (j : ℝ)| ≤ ε * (1 / 2) := by
        gcongr
        <;> exact hj_round
      linarith
    have hnorm2 : ‖y - g‖ ≤ ε := by
      have h_eucl : ∀ (z : Plane), ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
        intro z
        have h4 : ‖z‖ ^ 2 = ∑ i : Fin 2, z i ^ 2 := by
          rw [EuclideanSpace.norm_eq]
          rw [Real.sq_sqrt (by positivity)]
          apply Finset.sum_congr rfl
          intro i _
          have h5 : ‖z i‖ ^ 2 = (z i) ^ 2 := by
            simp [sq_abs]
          exact h5
        rw [h4, Fin.sum_univ_two] <;> ring
      have h3 : ‖y - g‖ ^ 2 = (y - g) 0 ^ 2 + (y - g) 1 ^ 2 := h_eucl (y - g)
      have h1 : (y - g) 0 ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith [abs_le.mp hdx]
      have h2 : (y - g) 1 ^ 2 ≤ (ε / 2) ^ 2 := by nlinarith [abs_le.mp hdy]
      have h4 : ‖y - g‖ ^ 2 ≤ ε ^ 2 := by
        rw [h3] <;> nlinarith
      have h5 : 0 ≤ ‖y - g‖ := by positivity
      have h6 : 0 ≤ ε := by linarith
      have h7 : |‖y - g‖| ≤ |ε| := sq_le_sq.mp h4
      rwa [abs_of_nonneg h5, abs_of_nonneg h6] at h7
    have hdist2 : dist y g ≤ ε := by simpa [dist_eq_norm] using hnorm2
    have hball : y ∈ Metric.closedBall g ε := hdist2
    exact Set.mem_iUnion₂.mpr ⟨g, hgS, hball⟩

/-- If external covering number is finite, a minimal cover attaining it exists. -/
lemma exists_minimal_external_cover
    {X : Type*} [PseudoMetricSpace X] {ε : NNReal} {A : Set X}
    (h : Metric.externalCoveringNumber ε A ≠ ⊤) :
    ∃ (C : Set X), Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
  classical
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
  have h_exists : ∃ (C : Set X), Metric.IsCover ε A C ∧ C.encard ≤ ↑n := by
    by_contra h'
    push Not at h'
    have h1 : ∀ (C : Set X), Metric.IsCover ε A C → (↑(n + 1) : ℕ∞) ≤ C.encard := by
      intro C hC
      have h2 : (↑n : ℕ∞) < C.encard := h' C hC
      by_cases h3 : C.encard = ⊤
      · rw [h3] <;> simp
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h3
        have h4 : (↑n : ℕ∞) < (↑m : ℕ∞) := by
          have h5 : C.encard = ↑m := hm.symm
          rw [h5] at h2 <;> exact h2
        have h5 : n < m := by exact_mod_cast h4
        have h6 : n + 1 ≤ m := by linarith
        have h7 : (↑(n + 1) : ℕ∞) ≤ (↑m : ℕ∞) := by exact_mod_cast h6
        have h8 : C.encard = ↑m := hm.symm
        rw [h8]
        exact h7
    have h3 : (↑(n + 1) : ℕ∞) ≤ Metric.externalCoveringNumber ε A := by
      simp only [Metric.externalCoveringNumber]
      apply le_iInf
      intro C
      apply le_iInf
      intro hC
      exact h1 C hC
    have h4 : (↑(n + 1) : ℕ∞) ≤ (↑n : ℕ∞) := by
      have h5 : Metric.externalCoveringNumber ε A = ↑n := hn.symm
      rw [h5] at h3
      exact h3
    have h_cont : ¬ (↑(n + 1) : ℕ∞) ≤ (↑n : ℕ∞) := by
      norm_cast <;> omega
    exact h_cont h4
  rcases h_exists with ⟨C, hC, hCencard⟩
  have h4 : C.encard ≤ Metric.externalCoveringNumber ε A := by
    have h41 : C.encard ≤ (↑n : ℕ∞) := hCencard
    rwa [← hn]
  have h5 : Metric.externalCoveringNumber ε A ≤ C.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hC
  have h6 : C.encard = Metric.externalCoveringNumber ε A := le_antisymm h4 h5
  exact ⟨C, hC, h6⟩

/-- External covering number is invariant under translation in EuclideanPlane. -/
lemma externalCoveringNumber_translation
    (v : Plane) {A : Set Plane} {ε : NNReal} :
    Metric.externalCoveringNumber ε ((fun x : Plane => x - v) '' A) =
    Metric.externalCoveringNumber ε A := by
  let τ : Plane → Plane := fun x => x - v
  let τinv : Plane → Plane := fun y => y + v
  have hτ_iso : Isometry τ := by
    intro x y
    rw [edist_dist, edist_dist]
    have h : dist (x - v) (y - v) = dist x y := by
      simp [dist_eq_norm] <;> abel
    rw [h]
  have hτinv_iso : Isometry τinv := by
    intro x y
    rw [edist_dist, edist_dist]
    have h : dist (x + v) (y + v) = dist x y := by
      simp [dist_eq_norm] <;> abel
    rw [h]
  have h_left : ∀ x, τinv (τ x) = x := by
    intro x
    simp [τ, τinv] <;> abel
  have h_image : τinv '' (τ '' A) = A := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [h_left x] <;> exact hx
    · intro hz
      exact ⟨τ z, ⟨z, hz, rfl⟩, h_left z⟩
  have h_forward : ∀ {B : Set Plane} {g : Plane → Plane}, Isometry g →
      Metric.externalCoveringNumber ε (g '' B) ≤ Metric.externalCoveringNumber ε B := by
    intro B g hg
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    have h2 : Metric.IsCover ε (g '' B) (g '' C) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have h3 : ∃ y ∈ C, edist x y ≤ ε := hC hx
      rcases h3 with ⟨y, hyC, hxy⟩
      have h4 : edist (g x) (g y) = edist x y := hg.edist_eq x y
      have h6 : edist (g x) (g y) ≤ ↑ε := by
        rw [h4] <;> exact hxy
      exact ⟨g y, Set.mem_image_of_mem g hyC, h6⟩
    have h4 : Metric.externalCoveringNumber ε (g '' B) ≤ (g '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h2
    have h5 : (g '' C).encard = C.encard := hg.injective.encard_image C
    exact le_trans h4 (le_of_eq h5)
  have h1 : Metric.externalCoveringNumber ε (τ '' A) ≤ Metric.externalCoveringNumber ε A :=
    h_forward (B := A) (g := τ) hτ_iso
  have h2 : Metric.externalCoveringNumber ε A ≤ Metric.externalCoveringNumber ε (τ '' A) := by
    have h4 := h_forward (B := τ '' A) (g := τinv) hτinv_iso
    rw [h_image] at h4
    exact h4
  exact le_antisymm h1 h2

/-- Given an ε-cover C of B, and every point of A is within ε/√2 of some point of B,
    refine C to an ε-cover of A with at most 25 * |C| balls. -/
lemma near_set_cover_refine
    {ε : NNReal} (hε : 0 < ε)
    {A B : Set Plane} {C : Set Plane} (hC : Metric.IsCover ε B C)
    (hnear : ∀ a ∈ A, ∃ b ∈ B, dist a b ≤ (ε : ℝ) / Real.sqrt 2) :
    ∃ (D : Set Plane), Metric.IsCover ε A D ∧ D.encard ≤ 25 * C.encard := by
  classical
  let S (c : Plane) : Finset Plane := (ball_covered_by_25 (NNReal.coe_pos.mp hε) c).choose
  have hS2 : ∀ c, Metric.closedBall c (snapCoverRatio * (ε : ℝ)) ⊆
      ⋃ y ∈ (S c), Metric.closedBall y (ε : ℝ) := fun c =>
    (ball_covered_by_25 (NNReal.coe_pos.mp hε) c).choose_spec.2
  let D : Set Plane := ⋃ c ∈ C, (S c : Set Plane)
  have hDcover : Metric.IsCover ε A D := by
    intro a ha
    rcases hnear a ha with ⟨b, hbB, hdist_ab⟩
    have hC_b : ∃ c ∈ C, edist b c ≤ ε := hC hbB
    rcases hC_b with ⟨c, hcC, hdist_bc⟩
    have hdist_bc' : dist b c ≤ (ε : ℝ) := by exact_mod_cast hdist_bc
    have hdist_ac : dist a c ≤ snapCoverRatio * (ε : ℝ) := by
      calc dist a c
        ≤ dist a b + dist b c := dist_triangle _ _ _
      _ ≤ (ε : ℝ) / Real.sqrt 2 + (ε : ℝ) := by gcongr
      _ = snapCoverRatio * (ε : ℝ) := by
        simp [snapCoverRatio] <;> ring
    have h_in_ball : a ∈ Metric.closedBall c (snapCoverRatio * (ε : ℝ)) := by
      simpa [Metric.mem_closedBall] using hdist_ac
    have h4 : a ∈ ⋃ y ∈ (S c), Metric.closedBall y (ε : ℝ) := hS2 c h_in_ball
    rcases Set.mem_iUnion₂.mp h4 with ⟨y, hyS, hyball⟩
    have hyD : y ∈ D := Set.mem_iUnion₂.mpr ⟨c, hcC, hyS⟩
    have hdist_y : dist a y ≤ (ε : ℝ) := by simpa [Metric.mem_closedBall] using hyball
    exact ⟨y, hyD, by exact_mod_cast hdist_y⟩
  have hDcard : D.encard ≤ 25 * C.encard := by
    by_cases hfin : C.Finite
    · let C' := hfin.toFinset
      let D' : Finset Plane := C'.biUnion S
      have hD_eq : (D' : Set Plane) = D := by
        ext z
        simp [D, D', C', hfin.mem_toFinset] <;> tauto
      rw [← hD_eq]
      have hS1 : ∀ c ∈ C', (S c).card = 25 := fun c _ =>
        (ball_covered_by_25 (NNReal.coe_pos.mp hε) c).choose_spec.1
      have h_card1 : D'.card ≤ ∑ c ∈ C', (S c).card := Finset.card_biUnion_le
      have h_card2 : (∑ c ∈ C', (S c).card) ≤ ∑ _ ∈ C', (25 : ℕ) := by
        gcongr
        <;> exact le_of_eq (hS1 c ‹_›)
      have h_card3 : (∑ _ ∈ C', (25 : ℕ)) = 25 * C'.card := by
        have h : (∑ _ ∈ C', (25 : ℕ)) = C'.card * 25 := by
          rw [Finset.sum_const]
          <;> ring
        rw [h] <;> ring
      have hCenc : C.encard = ↑C'.card := by exact Set.Finite.encard_eq_coe_toFinset_card hfin
      have h1 : (D' : Set Plane).encard = ↑D'.card := by exact Set.encard_coe_eq_coe_finsetCard D'
      rw [h1]
      have h3 : D'.card ≤ 25 * C'.card := calc D'.card
          ≤ ∑ c ∈ C', (S c).card := h_card1
        _ ≤ ∑ _ ∈ C', (25 : ℕ) := h_card2
        _ = 25 * C'.card := h_card3
      rw [hCenc]
      exact_mod_cast h3
    · have h : C.encard = ⊤ := by simpa [Set.encard_eq_top] using hfin
      rw [h] <;> simp
  exact ⟨D, hDcover, hDcard⟩

/-- Covering number of snapped image ≤ 25 * covering number of original (ℕ∞ version). -/
lemma ncover_snap_upper_nat
    {ε : NNReal} (hε : 0 < ε) {A : Set Plane}
    {f : Plane → Plane} (hf : ∀ a, dist a (f a) ≤ (ε : ℝ) / Real.sqrt 2) :
    Metric.externalCoveringNumber ε (f '' A) ≤ 25 * Metric.externalCoveringNumber ε A := by
  by_cases htop : Metric.externalCoveringNumber ε A = ⊤
  · rw [htop] <;> simp
  · rcases exists_minimal_external_cover htop with ⟨C, hC, hCeq⟩
    have hnear : ∀ z ∈ (f '' A), ∃ a ∈ A, dist z a ≤ (ε : ℝ) / Real.sqrt 2 := by
      intro z hz
      rcases hz with ⟨a, ha, rfl⟩
      exact ⟨a, ha, by simpa [dist_comm] using hf a⟩
    rcases near_set_cover_refine hε hC hnear with ⟨D, hDcover, hDcard⟩
    have h1 : Metric.externalCoveringNumber ε (f '' A) ≤ D.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hDcover
    have h2 : D.encard ≤ 25 * C.encard := hDcard
    rw [hCeq] at h2
    exact le_trans h1 h2

/-- Covering number of original ≤ 25 * covering number of snapped image (ℕ∞ version). -/
lemma ncover_snap_lower_nat
    {ε : NNReal} (hε : 0 < ε) {A : Set Plane}
    {f : Plane → Plane} (hf : ∀ a, dist a (f a) ≤ (ε : ℝ) / Real.sqrt 2) :
    Metric.externalCoveringNumber ε A ≤ 25 * Metric.externalCoveringNumber ε (f '' A) := by
  by_cases htop : Metric.externalCoveringNumber ε (f '' A) = ⊤
  · rw [htop] <;> simp
  · rcases exists_minimal_external_cover htop with ⟨C, hC, hCeq⟩
    have hnear : ∀ a ∈ A, ∃ z ∈ (f '' A), dist a z ≤ (ε : ℝ) / Real.sqrt 2 := by
      intro a ha
      exact ⟨f a, ⟨a, ha, rfl⟩, by simpa [dist_comm] using hf a⟩
    rcases near_set_cover_refine hε hC hnear with ⟨D, hDcover, hDcard⟩
    have h1 : Metric.externalCoveringNumber ε A ≤ D.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hDcover
    have h2 : D.encard ≤ 25 * C.encard := hDcard
    rw [hCeq] at h2
    exact le_trans h1 h2

/-- Snapped image intersected with a ball is contained in the snapped image of
    the original intersected with an expanded ball. -/
lemma snap_image_inter_subset
    {ε : ℝ} (hε : 0 < ε) {A : Set Plane} {f : Plane → Plane}
    (hf : ∀ a, dist a (f a) ≤ ε / Real.sqrt 2)
    {x : Plane} {R : ℝ} :
    (f '' A) ∩ Metric.closedBall x R ⊆ f '' (A ∩ Metric.closedBall x (R + ε / Real.sqrt 2)) := by
  intro z hz
  rcases hz.1 with ⟨a, ha, rfl⟩
  have hdist : dist (f a) x ≤ R := by simpa [Metric.mem_closedBall] using hz.2
  have hdist2 : dist a x ≤ R + ε / Real.sqrt 2 := by
    calc dist a x
      ≤ dist a (f a) + dist (f a) x := dist_triangle _ _ _
    _ ≤ ε / Real.sqrt 2 + R := by
      have hfa : dist a (f a) ≤ ε / Real.sqrt 2 := hf a
      linarith
    _ = R + ε / Real.sqrt 2 := by ring
  exact ⟨a, ⟨ha, by simpa [Metric.mem_closedBall] using hdist2⟩, rfl⟩

/-- External covering number of scaled+translated set. -/
lemma ncover_affine_scale
    {Δ : ℝ} (hΔ : 0 < Δ) {δ : ℝ} (hδ : 0 < δ) (hδ_eq : δ = Δ^2)
    (T0 : Plane) (A : Set Plane) :
    Metric.externalCoveringNumber δ.toNNReal ((fun p : Plane => Δ • (p - T0)) '' A) =
      Metric.externalCoveringNumber Δ.toNNReal A := by
  let τ : Plane → Plane := fun p => p - T0
  let σ : Plane → Plane := fun p => Δ • p
  have hτ_iso : Isometry τ := by
    intro x y
    simp [τ, dist_eq_norm] <;> abel
  have hφ : (fun p : Plane => Δ • (p - T0)) = σ ∘ τ := by funext p; rfl
  have h_comp : (σ ∘ τ) '' A = σ '' (τ '' A) := by
    rw [Set.image_comp]
  have h1 : Metric.externalCoveringNumber δ.toNNReal ((fun p : Plane => Δ • (p - T0)) '' A) =
      Metric.externalCoveringNumber δ.toNNReal (σ '' (τ '' A)) := by
    rw [hφ, h_comp]
  rw [h1]
  have h2 : Metric.externalCoveringNumber δ.toNNReal (σ '' (τ '' A)) =
      Metric.externalCoveringNumber ((δ / Δ).toNNReal) (τ '' A) := by
    have h_pos : 0 < δ / Δ := by positivity
    have h4 : (⟨Δ, hΔ.le⟩ * (δ / Δ).toNNReal : NNReal) = δ.toNNReal := by
      apply NNReal.coe_injective
      have h_pos2 : 0 ≤ δ / Δ := by positivity
      have h_coe1 : (((δ / Δ).toNNReal : ℝ)) = δ / Δ := by
        simp [Real.toNNReal, h_pos2]
      let cΔ : NNReal := ⟨Δ, hΔ.le⟩
      have hcΔ : (cΔ : ℝ) = Δ := by
        dsimp only [cΔ]
        <;> rfl
      have h_coe_mul : ((cΔ * (δ / Δ).toNNReal : NNReal) : ℝ) =
          (cΔ : ℝ) * ((δ / Δ).toNNReal : ℝ) := by
        exact_mod_cast NNReal.coe_mul _ _
      have h_coe2 : ((δ.toNNReal : ℝ)) = δ := by
        simp [Real.toNNReal, hδ.le]
      rw [h_coe_mul, h_coe1, h_coe2, hcΔ]
      <;> field_simp [hΔ.ne']
    have h5 := externalCoveringNumber_smul (c := Δ) hΔ (ε := (δ / Δ).toNNReal) (A := τ '' A)
    rw [h4] at h5
    exact h5
  rw [h2]
  have h3 : δ / Δ = Δ := by
    rw [hδ_eq] <;> field_simp [hΔ.ne'] <;> ring
  rw [h3]
  exact externalCoveringNumber_translation (v := T0)

/-- Intersection of scaled+translated set with a ball. -/
lemma affine_scale_inter
    {Δ : ℝ} (hΔ : 0 < Δ) (T0 : Plane) {x : Plane} {r : ℝ} (hr : 0 ≤ r)
    (T : Set Plane) :
    ((fun p : Plane => Δ • (p - T0)) '' T) ∩ Metric.closedBall x (Δ * r) =
    (fun p : Plane => Δ • (p - T0)) '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r) := by
  let τ : Plane → Plane := fun p => p - T0
  let σ : Plane → Plane := fun p => Δ • p
  let φ : Plane → Plane := fun p => Δ • (p - T0)
  have hφ : φ = σ ∘ τ := by funext p; rfl
  have h_image : φ '' T = σ '' (τ '' T) := by
    ext z
    simp [φ, σ, τ, Set.mem_image] <;> tauto
  have h_main1 : (φ '' T) ∩ Metric.closedBall x (Δ * r) =
      σ '' ((τ '' T) ∩ Metric.closedBall (Δ⁻¹ • x) r) := by
    rw [h_image]
    have h_smul := smul_closedBall_inter (c := Δ) hΔ (A := τ '' T) (y := x) (r := Δ * r) (by positivity)
    have hdiv : (Δ * r) / Δ = r := by field_simp [hΔ.ne'] <;> ring
    rw [hdiv] at h_smul
    exact h_smul
  have h_main2 : (τ '' T) ∩ Metric.closedBall (Δ⁻¹ • x) r =
      τ '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hball⟩
      have h4 : dist (τ p) (Δ⁻¹ • x) ≤ r := hball
      have h5 : dist p (T0 + Δ⁻¹ • x) ≤ r := by
        have h6 : dist (τ p) (Δ⁻¹ • x) = dist p (T0 + Δ⁻¹ • x) := by
          simp [τ, dist_eq_norm, sub_sub] <;> abel
        rw [h6] at h4
        exact h4
      exact ⟨p, ⟨hp, by simpa [Metric.mem_closedBall] using h5⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hball⟩, rfl⟩
      have h4 : dist p (T0 + Δ⁻¹ • x) ≤ r := by simpa [Metric.mem_closedBall] using hball
      have h5 : dist (τ p) (Δ⁻¹ • x) ≤ r := by
        have h6 : dist (τ p) (Δ⁻¹ • x) = dist p (T0 + Δ⁻¹ • x) := by
          simp [τ, dist_eq_norm, sub_sub] <;> abel
        rw [h6]
        exact h4
      exact ⟨⟨p, hp, rfl⟩, by simpa [Metric.mem_closedBall] using h5⟩
  have h_final : σ '' (τ '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r)) =
      φ '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r) := by
    ext z
    simp [φ, σ, τ, Set.mem_image] <;> tauto
  rw [h_main1, h_main2, h_final]

/-- Main transfer theorem: a (Δ,s,C)-set, after affine scaling by Δ and snapping
    to the δ-grid (δ=Δ²), yields an IsRescalableDeltaSet with degraded constant. -/
theorem sset_transfer_affine_snap
    (Δ δ s C : ℝ) (hΔ : 0 < Δ) (hδ : 0 < δ) (hδ_eq : δ = Δ^2)
    (hs : 0 ≤ s) (hC : 0 < C)
    (T : Set Plane) (hT : IsDeltaSSet Δ s C T)
    (T0 : Plane)
    (snap : Plane → Plane)
    (hsnap : ∀ p, dist p (snap p) ≤ δ / Real.sqrt 2) :
    IsRescalableDeltaSet δ Δ s (625 * (1 + 1 / Real.sqrt 2)^s * C)
      (snap '' ((fun p : Plane => Δ • (p - T0)) '' T)) := by
  let φ : Plane → Plane := fun p => Δ • (p - T0)
  let P : Set Plane := φ '' T
  let P' : Set Plane := snap '' P
  have hT_nonempty : T.Nonempty := hT.1
  have hP_nonempty : P.Nonempty := hT_nonempty.image φ
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image snap
  have hδ_toNNReal_pos : 0 < δ.toNNReal := by
    have h : (δ.toNNReal : ℝ) = δ := by
      simp [Real.toNNReal, hδ.le]
    exact Real.toNNReal_pos.mpr hδ
  have hC' : 0 < 625 * (1 + 1 / Real.sqrt 2)^s * C := by positivity
  have hsnap' : ∀ p, dist p (snap p) ≤ (δ.toNNReal : ℝ) / Real.sqrt 2 := by
    intro p
    have h_eq : (δ.toNNReal : ℝ) = δ := by simp [Real.toNNReal, hδ.le]
    rw [h_eq]
    exact hsnap p

  -- Step 1: P satisfies IsRescalableDeltaSet δ Δ s C P
  have hP_rescalable : IsRescalableDeltaSet δ Δ s C P := by
    refine ⟨hP_nonempty, hδ, hΔ, hC, hs, fun x r hr => ?_⟩
    have h_inter : P ∩ Metric.closedBall x (Δ * r) =
        φ '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r) :=
      affine_scale_inter hΔ T0 (hr := by linarith) T
    rw [h_inter]
    have h4 : Metric.externalCoveringNumber δ.toNNReal
          (φ '' (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r)) =
        Metric.externalCoveringNumber Δ.toNNReal
          (T ∩ Metric.closedBall (T0 + Δ⁻¹ • x) r) :=
      ncover_affine_scale hΔ hδ hδ_eq T0 _
    rw [h4]
    have h5 := hT.2.2.2.2 (T0 + Δ⁻¹ • x) r hr
    have h6 : Metric.externalCoveringNumber Δ.toNNReal T =
        Metric.externalCoveringNumber δ.toNNReal P :=
      (ncover_affine_scale hΔ hδ hδ_eq T0 T).symm
    rw [h6] at h5
    exact h5

  -- Step 2: Covering number bounds for snapping (in ℝ≥0∞)
  have h_upper_nat : Metric.externalCoveringNumber δ.toNNReal P' ≤
      25 * Metric.externalCoveringNumber δ.toNNReal P :=
    ncover_snap_upper_nat hδ_toNNReal_pos hsnap'
  have h_lower_nat : Metric.externalCoveringNumber δ.toNNReal P ≤
      25 * Metric.externalCoveringNumber δ.toNNReal P' :=
    ncover_snap_lower_nat hδ_toNNReal_pos hsnap'
  have h_upper : (Metric.externalCoveringNumber δ.toNNReal P' : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by
    exact_mod_cast h_upper_nat
  have h_lower : (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P' : ℝ≥0∞) := by
    exact_mod_cast h_lower_nat

  -- Step 3: Main intersection bound for P'
  refine ⟨hP'_nonempty, hδ, hΔ, hC', hs, fun x r hr => ?_⟩
  set r' : ℝ := r + Δ / Real.sqrt 2 with hr'_def
  have h_r_nonneg : 0 ≤ r := by linarith
  have hr'_ge : Δ ≤ r' := by
    dsimp only [r']
    have h_pos : 0 < Δ / Real.sqrt 2 := by positivity
    linarith
  have hr'_le : r' ≤ (1 + 1 / Real.sqrt 2) * r := by
    dsimp only [r']
    have h1 : Δ ≤ r := hr
    have h2 : 0 ≤ r := by linarith
    have h3 : Δ / Real.sqrt 2 ≤ r / Real.sqrt 2 := by
      have h4 : 0 < Real.sqrt 2 := by positivity
      gcongr
    have h5 : r + Δ / Real.sqrt 2 ≤ r + r / Real.sqrt 2 := by linarith
    have h6 : r + r / Real.sqrt 2 = (1 + 1 / Real.sqrt 2) * r := by ring
    linarith
  have hR_expand : Δ * r + δ / Real.sqrt 2 = Δ * r' := by
    dsimp only [r']
    rw [hδ_eq] <;> ring
  have h_inter1 : (P' ∩ Metric.closedBall x (Δ * r)) ⊆
      snap '' (P ∩ Metric.closedBall x (Δ * r + δ / Real.sqrt 2)) :=
    snap_image_inter_subset hδ hsnap
  have h_set_eq : snap '' (P ∩ Metric.closedBall x (Δ * r + δ / Real.sqrt 2)) =
      snap '' (P ∩ Metric.closedBall x (Δ * r')) := by
    rw [hR_expand]
  have h_cover1 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x (Δ * r)) : ℝ≥0∞) ≤
      (Metric.externalCoveringNumber δ.toNNReal
        (snap '' (P ∩ Metric.closedBall x (Δ * r'))) : ℝ≥0∞) := by
    have h := Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_inter1
    rw [h_set_eq] at h
    exact_mod_cast h
  have h_cover2 : (Metric.externalCoveringNumber δ.toNNReal
        (snap '' (P ∩ Metric.closedBall x (Δ * r'))) : ℝ≥0∞) ≤
      (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall x (Δ * r')) : ℝ≥0∞) := by
    exact_mod_cast ncover_snap_upper_nat hδ_toNNReal_pos hsnap'
  have h_rescalable : (Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall x (Δ * r')) : ℝ≥0∞) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) :=
    hP_rescalable.2.2.2.2.2 x r' hr'_ge
  have h_rpow_mono : (ENNReal.ofReal r') ^ s ≤ (ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r)) ^ s := by
    gcongr
    <;> linarith
  have hpos1 : 0 < 1 + 1 / Real.sqrt 2 := by positivity
  have h_expand : ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r) ^ s =
      ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * (ENNReal.ofReal r) ^ s := by
    have h9 : ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r) =
        ENNReal.ofReal (1 + 1 / Real.sqrt 2) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul hpos1.le] <;> ring
    rw [h9]
    have h10 : (ENNReal.ofReal (1 + 1 / Real.sqrt 2) * ENNReal.ofReal r) ^ s =
        (ENNReal.ofReal (1 + 1 / Real.sqrt 2)) ^ s * (ENNReal.ofReal r) ^ s :=
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
    rw [h10]
    have h11 : (ENNReal.ofReal (1 + 1 / Real.sqrt 2)) ^ s =
        ENNReal.ofReal ((1 + 1 / Real.sqrt 2) ^ s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hpos1.le (by linarith)]
    rw [h11]
  calc (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x (Δ * r)) : ℝ≥0∞)
    ≤ (Metric.externalCoveringNumber δ.toNNReal
          (snap '' (P ∩ Metric.closedBall x (Δ * r')))) := h_cover1
  _ ≤ (25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall x (Δ * r'))) := h_cover2
  _ ≤ (25 : ℝ≥0∞) * (ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P)) := by
    gcongr
    <;> exact h_rescalable
  _ ≤ (25 : ℝ≥0∞) * (ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r)) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P)) := by
    gcongr
  _ = (25 : ℝ≥0∞) * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P)) := by
    have h_goal : ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2) * r)) ^ s =
        ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s := by
      rw [h_expand]
      have h_comm : ENNReal.ofReal C * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * (ENNReal.ofReal r) ^ s) =
          (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ s := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_comm]
      have h10 : ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s) * ENNReal.ofReal C =
          ENNReal.ofReal (((1 + 1 / Real.sqrt 2)^s) * C) := by
        rw [← ENNReal.ofReal_mul (show 0 ≤ (1 + 1 / Real.sqrt 2)^s by positivity)]
      rw [h10]
    rw [h_goal]
    <;> ring
  _ ≤ (25 : ℝ≥0∞) * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s *
          ((25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P'))) := by
    gcongr
    <;> exact h_lower
  _ = ENNReal.ofReal (625 * (1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P') := by
    have h11 : (625 : ℝ≥0∞) = ENNReal.ofReal (625 : ℝ) := by norm_num
    have h13 : ENNReal.ofReal (625 : ℝ) * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) =
        ENNReal.ofReal (625 * ((1 + 1 / Real.sqrt 2)^s * C)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    have h14 : (25 : ℝ≥0∞) * (25 : ℝ≥0∞) = (625 : ℝ≥0∞) := by norm_num
    have h_final : (25 : ℝ≥0∞) * (ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s * ((25 : ℝ≥0∞) * (Metric.externalCoveringNumber δ.toNNReal P'))) =
        (625 : ℝ≥0∞) * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P') := by
      simp [h14, mul_assoc, mul_comm, mul_left_comm]
      <;> ring
    rw [h_final]
    have h11 : (625 : ℝ≥0∞) = ENNReal.ofReal (625 : ℝ) := by norm_num
    have h13 : ENNReal.ofReal (625 : ℝ) * ENNReal.ofReal ((1 + 1 / Real.sqrt 2)^s * C) =
        ENNReal.ofReal (625 * ((1 + 1 / Real.sqrt 2)^s * C)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h11, h13]
    have h15 : 625 * ((1 + 1 / Real.sqrt 2)^s * C) = 625 * (1 + 1 / Real.sqrt 2)^s * C := by ring
    rw [h15]
    <;> simp [mul_assoc, mul_comm, mul_left_comm]

end
