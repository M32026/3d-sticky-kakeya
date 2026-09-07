module

/-
  Bounded productProp from A.7 axiom.

  Proves a bounded version of productProp directly from
  `product_like_incidence_sum_product` (OS Proposition A.7).

  ## Key translations
  1. Coordinate transform maps bounded sets into A.7's normalized ranges
  2. IsDeltaSSet → IsDeltaSCSet via covering number comparability
  3. Parameter sets → appendixDyadicTubes families with exact incidence
  4. Encard conclusion → metric covering number conclusion

  ## Main theorem
  `productProp_bounded`: same as productProp but with explicit boundedness.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GridSnap
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.CoveringUtils
open DiscretisedFurstenbergEstimate.Translation

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Helper lemmas for scaling -/

lemma real_homothety_dist (lam : ℝ) (hlam : 0 < lam) (x y : ℝ) :
    dist (lam * x) (lam * y) = lam * dist x y := by
  have h : dist (lam * x) (lam * y) = |lam * x - lam * y| := by
    simp [dist_eq_norm]
  rw [h]
  have h2 : |lam * x - lam * y| = |lam * (x - y)| := by ring_nf
  rw [h2]
  have h3 : |lam * (x - y)| = |lam| * |x - y| := abs_mul lam (x - y)
  rw [h3]
  have h4 : |lam| = lam := abs_of_pos hlam
  rw [h4] <;> rfl

lemma nnreal_mul_toNNReal_general (a_nn : NNReal) (b : ℝ) (hb : 0 < b) :
    a_nn * b.toNNReal = ((a_nn : ℝ) * b).toNNReal := by
  have hb' : 0 ≤ b := by linarith
  have hab' : 0 ≤ (a_nn : ℝ) * b := by positivity
  apply Subtype.ext
  have h1 : (↑(a_nn * b.toNNReal) : ℝ) = (a_nn : ℝ) * b := by
    simp [NNReal.coe_mul, Real.coe_toNNReal', hb'] <;> ring
  have h2 : (↑(((a_nn : ℝ) * b).toNNReal) : ℝ) = (a_nn : ℝ) * b := by
    rw [Real.coe_toNNReal', max_eq_left hab']
  exact h1.trans h2.symm

lemma nnreal_inv_mul_toNNReal_general (a_nn : NNReal) (ha_pos : 0 < (a_nn : ℝ))
    (b : ℝ) (hb : 0 < b) :
    a_nn⁻¹ * ((a_nn : ℝ) * b).toNNReal = b.toNNReal := by
  have hb' : 0 ≤ b := by linarith
  have hab' : 0 ≤ (a_nn : ℝ) * b := by positivity
  apply Subtype.ext
  have h1 : (↑(a_nn⁻¹ * ((a_nn : ℝ) * b).toNNReal) : ℝ) = b := by
    simp [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal', hab']
    <;> field_simp [ha_pos.ne'] <;> ring
  have h2 : (↑(b.toNNReal) : ℝ) = b := by
    rw [Real.coe_toNNReal', max_eq_left hb']
  exact h1.trans h2.symm

lemma image_closedBall_homothety (lam : ℝ) (hlam : 0 < lam) (x r : ℝ) :
    (fun z : ℝ => lam * z) '' Metric.closedBall x r =
      Metric.closedBall (lam * x) (lam * r) := by
  let f : ℝ → ℝ := fun z => lam * z
  have h1 : ∀ z : ℝ, z ∈ Metric.closedBall x r ↔ f z ∈ Metric.closedBall (f x) (lam * r) := by
    intro z
    simp only [Metric.mem_closedBall]
    have h2 : dist (f z) (f x) = lam * dist z x := real_homothety_dist lam hlam z x
    rw [h2]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h (by linarith)
    · intro h; nlinarith
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact (h1 z).mp hz
  · intro hy
    refine ⟨y / lam, ?_, ?_⟩
    · have h3 : f (y / lam) = y := by simp [f]; field_simp [hlam.ne'] <;> ring
      have h4 : f (y / lam) ∈ Metric.closedBall (f x) (lam * r) := by rw [h3]; exact hy
      exact (h1 (y / lam)).mpr h4
    · field_simp [hlam.ne'] <;> ring

lemma prod_homothety_dist (lam : ℝ) (hlam : 0 < lam) (p q : ℝ × ℝ) :
    dist (lam * p.1, lam * p.2) (lam * q.1, lam * q.2) = lam * dist p q := by
  have h2 : dist (lam * p.1) (lam * q.1) = lam * dist p.1 q.1 :=
    real_homothety_dist lam hlam p.1 q.1
  have h3 : dist (lam * p.2) (lam * q.2) = lam * dist p.2 q.2 :=
    real_homothety_dist lam hlam p.2 q.2
  have h4 : dist (lam * p.1, lam * p.2) (lam * q.1, lam * q.2) =
      max (dist (lam * p.1) (lam * q.1)) (dist (lam * p.2) (lam * q.2)) := by
    simp [Prod.dist_eq]
  rw [h4, h2, h3]
  have h5 : max (lam * dist p.1 q.1) (lam * dist p.2 q.2) =
      lam * max (dist p.1 q.1) (dist p.2 q.2) := by
    by_cases h : dist p.1 q.1 ≤ dist p.2 q.2
    · have h_scaled : lam * dist p.1 q.1 ≤ lam * dist p.2 q.2 :=
        mul_le_mul_of_nonneg_left h (by linarith)
      rw [max_eq_right h, max_eq_right h_scaled]
    · have h' : dist p.2 q.2 < dist p.1 q.1 := by exact lt_of_not_ge h
      have h_scaled : lam * dist p.2 q.2 < lam * dist p.1 q.1 :=
        mul_lt_mul_of_pos_left h' hlam
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  rw [h5] <;> simp [Prod.dist_eq]

lemma image_closedBall_homothety_general {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (lam : ℝ) (hlam : 0 < lam)
    (hdist : ∀ x y, dist (f x) (f y) = lam * dist x y)
    (hsurj : Function.Surjective f) (x : X) (r : ℝ) :
    f '' Metric.closedBall x r = Metric.closedBall (f x) (lam * r) := by
  have h1 : ∀ z, z ∈ Metric.closedBall x r ↔ f z ∈ Metric.closedBall (f x) (lam * r) := by
    intro z
    simp only [Metric.mem_closedBall]
    have h2 : dist (f z) (f x) = lam * dist z x := hdist z x
    rw [h2]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h (by linarith)
    · intro h; nlinarith
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact (h1 z).mp hz
  · intro hy
    rcases hsurj y with ⟨z, rfl⟩
    exact ⟨z, (h1 z).mpr hy, rfl⟩

/-! ### Translation and scaling lemmas for IsDeltaSSet -/

/-- Transform y-coordinate: [-1,1] → [0,1]. -/
def transformY (y : ℝ) : ℝ := (y + 1) / 2

/-- Transform x-coordinate: [-1,1] → [0,1/2]. -/
def transformX (x : ℝ) : ℝ := (x + 1) / 4

/-- Transform tube parameters (a,b) to fit A.7's parameter strip.
    (a,b) ↦ (a/2, (b-a+1)/4).
    Preserves incidence up to factor 1/4:
    |a'*y' + b' - x'| = |a*y + b - x| / 4. -/
def transformTube (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / 2, (p.2 - p.1 + 1) / 4)

lemma transformY_range {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1) :
    0 ≤ transformY y ∧ transformY y ≤ 1 := by
  have h1 : -1 ≤ y := hy.1
  have h2 : y ≤ 1 := hy.2
  have h3 : transformY y = (y + 1) / 2 := by rfl
  rw [h3]
  exact ⟨by linarith, by linarith⟩

lemma transformX_range {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) :
    0 ≤ transformX x ∧ transformX x ≤ 1 / 2 := by
  have h1 : -1 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : transformX x = (x + 1) / 4 := by rfl
  rw [h3]
  exact ⟨by linarith, by linarith⟩

lemma transformTube_range {a b : ℝ}
    (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2) :
    -1 ≤ (transformTube (a, b)).1 ∧ (transformTube (a, b)).1 ≤ 1 ∧
    -3 / 4 ≤ (transformTube (a, b)).2 ∧ (transformTube (a, b)).2 ≤ 5 / 4 := by
  have ha1 : -2 ≤ a := ha.1
  have ha2 : a ≤ 2 := ha.2
  have hb1 : -2 ≤ b := hb.1
  have hb2 : b ≤ 2 := hb.2
  set a' := (transformTube (a, b)).1 with ha'
  set b' := (transformTube (a, b)).2 with hb'
  have ha'_eq : a' = a / 2 := by simp [ha', transformTube]
  have hb'_eq : b' = (b - a + 1) / 4 := by simp [hb', transformTube]
  rw [ha'_eq, hb'_eq]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Incidence preservation under coordinate transformation. -/
lemma incidence_transformed (δ a b x y : ℝ)
    (h : |a * y + b - x| ≤ 2 * δ) :
    |(transformTube (a, b)).1 * transformY y +
      (transformTube (a, b)).2 - transformX x| ≤ δ / 2 := by
  have h_eq : (transformTube (a, b)).1 * transformY y +
      (transformTube (a, b)).2 - transformX x = (a * y + b - x) / 4 := by
    simp [transformTube, transformY, transformX] <;> ring
  rw [h_eq]
  have h1 : |(a * y + b - x) / 4| ≤ δ / 2 := by
    have h2 : |a * y + b - x| ≤ 2 * δ := h
    have h3 : |(a * y + b - x) / 4| = |a * y + b - x| / 4 := by
      rw [abs_div] <;> norm_num
    rw [h3]
    linarith
  exact h1

/-! ### Critical geometric lemma: approximate incidence → dyadic tube -/

/-- Convert a point in ℝ×ℝ to EuclideanSpace ℝ (Fin 2). -/
def toEuclidean (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.1, p.2]

lemma toEuclidean_apply (p : ℝ × ℝ) :
    (toEuclidean p) 0 = p.1 ∧ (toEuclidean p) 1 = p.2 := by
  simp [toEuclidean] <;> aesop

/-- Given z = (x,y) in [0,1]² and p = (a,b) with a ∈ [-1,1], b bounded, and
|a*y+b-x| ≤ δ/2, there exists a dyadic cube C at scale δ such that:
1. C meets the parameter strip (its a-range intersects [-1,1])
2. z ∈ appendixDualOfParameterSet C (exact incidence)
3. C is within 3δ of p in L∞ distance -/
lemma approximate_to_exact_incidence (δ : ℝ) (hδ : 0 < δ)
    (x y a b : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -2 ≤ b ∧ b ≤ 2)
    (h_inc : |a * y + b - x| ≤ δ / 2) :
    ∃ (k : Fin 2 → ℤ),
      let C := dyadicCube δ k
      (C ∩ appendixParameterStrip).Nonempty ∧
      (toEuclidean (x, y)) ∈ appendixDualOfParameterSet C ∧
      a ∈ Set.Ico (δ * (k 0)) (δ * ((k 0 : ℝ) + 1)) ∧
      b ∈ Set.Icc (δ * (k 1) - 3 * δ) (δ * ((k 1 : ℝ) + 1) + 3 * δ) := by
  -- Choose i = floor(a/δ)
  let i : ℤ := ⌊a / δ⌋
  have hi1 : δ * (i : ℝ) ≤ a := by
    have h : (i : ℝ) ≤ a / δ := Int.floor_le _
    have h' : δ * (i : ℝ) ≤ δ * (a / δ) := by gcongr
    have h'' : δ * (a / δ) = a := by
      field_simp [hδ.ne'] <;> ring
    rw [h''] at h'
    exact h'
  have hi2 : a < δ * ((i : ℝ) + 1) := by
    have h : a / δ < ((i : ℝ) + 1) := Int.lt_floor_add_one _
    have h' : δ * (a / δ) < δ * (((i : ℝ) + 1)) := by gcongr
    have h'' : δ * (a / δ) = a := by
      field_simp [hδ.ne'] <;> ring
    rw [h''] at h'
    exact h'

  -- b_line = x - i*δ*y
  let b_line : ℝ := x - δ * (i : ℝ) * y
  have h_bl1 : |b_line - b| ≤ 3 * δ / 2 := by
    have h1 : b_line - b = (x - a * y - b) + (a - δ * (i : ℝ)) * y := by
      simp [b_line] <;> ring
    rw [h1]
    have h2 : |x - a * y - b| ≤ δ / 2 := by
      have h21 : |a * y + b - x| ≤ δ / 2 := h_inc
      have h22 : x - a * y - b = -(a * y + b - x) := by ring
      rw [h22, abs_neg]
      exact h21
    have h4 : |a - δ * (i : ℝ)| < δ := by
      rw [abs_sub_lt_iff] <;> constructor <;> linarith
    have h5 : 0 ≤ y := hy.1
    have h6 : y ≤ 1 := hy.2
    have h7 : |(a - δ * (i : ℝ)) * y| ≤ δ := by
      have h71 : |(a - δ * (i : ℝ)) * y| = |a - δ * (i : ℝ)| * y := by
        rw [abs_mul, abs_of_nonneg h5]
      rw [h71]
      have h72 : |a - δ * (i : ℝ)| * y ≤ |a - δ * (i : ℝ)| := by
        have h73 : y ≤ 1 := h6
        nlinarith [abs_nonneg (a - δ * (i : ℝ))]
      have h74 : |a - δ * (i : ℝ)| < δ := h4
      linarith
    have h8 : |(x - a * y - b) + (a - δ * (i : ℝ)) * y| ≤
        |x - a * y - b| + |(a - δ * (i : ℝ)) * y| := by
      exact abs_add_le (x - a * y - b) ((a - δ * ↑i) * y)
    linarith

  -- Choose j = floor(b_line/δ)
  let j : ℤ := ⌊b_line / δ⌋
  have hj1 : δ * (j : ℝ) ≤ b_line := by
    have h : (j : ℝ) ≤ b_line / δ := Int.floor_le _
    have h' : δ * (j : ℝ) ≤ δ * (b_line / δ) := by gcongr
    have h'' : δ * (b_line / δ) = b_line := by
      field_simp [hδ.ne'] <;> ring
    rw [h''] at h'
    exact h'
  have hj2 : b_line < δ * ((j : ℝ) + 1) := by
    have h : b_line / δ < ((j : ℝ) + 1) := Int.lt_floor_add_one _
    have h' : δ * (b_line / δ) < δ * (((j : ℝ) + 1)) := by gcongr
    have h'' : δ * (b_line / δ) = b_line := by
      field_simp [hδ.ne'] <;> ring
    rw [h''] at h'
    exact h'

  let k : Fin 2 → ℤ := fun idx =>
    match idx with
    | 0 => i
    | 1 => j
  have hk0 : k 0 = i := by simp [k]
  have hk1 : k 1 = j := by simp [k]

  refine ⟨k, ?_, ?_, ?_, ?_⟩

  · -- C meets parameter strip
    let p_C : EuclideanSpace ℝ (Fin 2) := toEuclidean (a, b_line)
    have h_pC0 : p_C 0 = a := (toEuclidean_apply (a, b_line)).1
    have h_pC1 : p_C 1 = b_line := (toEuclidean_apply (a, b_line)).2
    have h_pC_in_C : p_C ∈ dyadicCube δ k := by
      simp only [dyadicCube, Set.mem_setOf_eq]
      intro idx
      fin_cases idx
      · -- idx = 0
        simp [hk0, h_pC0] <;> exact ⟨hi1, hi2⟩
      · -- idx = 1
        simp [hk1, h_pC1] <;> exact ⟨hj1, hj2⟩
    have h_pC_strip : p_C ∈ appendixParameterStrip := by
      simp [appendixParameterStrip, h_pC0, ha.1, ha.2] <;> tauto
    exact ⟨p_C, h_pC_in_C, h_pC_strip⟩

  · -- z ∈ dual(C)
    let p_line : EuclideanSpace ℝ (Fin 2) := toEuclidean (δ * (i : ℝ), b_line)
    have h_pl0 : p_line 0 = δ * (i : ℝ) := (toEuclidean_apply (δ * (i : ℝ), b_line)).1
    have h_pl1 : p_line 1 = b_line := (toEuclidean_apply (δ * (i : ℝ), b_line)).2
    have h_pline_C : p_line ∈ dyadicCube δ k := by
      simp only [dyadicCube, Set.mem_setOf_eq]
      intro idx
      fin_cases idx
      · -- idx = 0
        have h_goal : p_line 0 ∈ Set.Ico (δ * (k 0)) (δ * ((k 0 : ℝ) + 1)) := by
          rw [hk0, h_pl0]
          exact ⟨by linarith, by linarith [hδ]⟩
        exact h_goal
      · -- idx = 1
        have h_goal : p_line 1 ∈ Set.Ico (δ * (k 1)) (δ * ((k 1 : ℝ) + 1)) := by
          rw [hk1, h_pl1]
          exact ⟨hj1, hj2⟩
        exact h_goal
    let z_eucl : EuclideanSpace ℝ (Fin 2) := toEuclidean (x, y)
    have h_z0 : z_eucl 0 = x := (toEuclidean_apply (x, y)).1
    have h_z1 : z_eucl 1 = y := (toEuclidean_apply (x, y)).2
    have h_pline_inc : p_line 0 * z_eucl 1 + p_line 1 = z_eucl 0 := by
      rw [h_pl0, h_pl1, h_z0, h_z1]
      <;> simp [b_line] <;> ring
    have h_z_in_dual : z_eucl ∈ appendixDualOfParameterSet (dyadicCube δ k) := by
      refine ⟨p_line, h_pline_C, ?_⟩
      have h_eq : z_eucl 0 = p_line 0 * z_eucl 1 + p_line 1 := Eq.symm h_pline_inc
      simpa [appendixDualLineMap, appendixDualLine] using h_eq
    exact h_z_in_dual

  · -- a is in the cube's a-range
    simpa [hk0] using ⟨hi1, hi2⟩

  · -- b is within 3δ of the cube's b-range
    have h4 : b ≥ δ * (j : ℝ) - 3 * δ := by
      have h5 : |b_line - b| ≤ 3 * δ / 2 := h_bl1
      have h6 : b_line - b ≤ 3 * δ / 2 := (abs_le.mp h5).2
      linarith [hj1]
    have h7 : b ≤ δ * ((j : ℝ) + 1) + 3 * δ := by
      have h8 : |b_line - b| ≤ 3 * δ / 2 := h_bl1
      have h9 : -(3 * δ / 2) ≤ b_line - b := (abs_le.mp h8).1
      have h10 : b ≤ b_line + 3 * δ / 2 := by linarith
      linarith [hj2]
    have h_goal : b ∈ Set.Icc (δ * (k 1) - 3 * δ) (δ * ((k 1 : ℝ) + 1) + 3 * δ) := by
      rw [hk1]
      exact ⟨h4, h7⟩
    exact h_goal

/-! ### 1D covering number comparability -/

/-- A δ-ball in ℝ intersects at most 3 dyadic δ-intervals.
Returns a finset of at most 3 integers containing all k whose δ-interval
meets [x-δ, x+δ]. -/
lemma ball_intersects_three_cubes (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    ∃ (S : Finset ℤ), S.card ≤ 3 ∧
      ∀ (k : ℤ), (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩
        Set.Icc (x - δ) (x + δ)).Nonempty → k ∈ S := by
  let m : ℤ := ⌊x / δ⌋
  let S : Finset ℤ := {m - 1, m, m + 1}
  have hS3 : S.card = 3 := by
    have h1 : (m - 1 : ℤ) ≠ m := by omega
    have h2 : (m - 1 : ℤ) ≠ m + 1 := by omega
    have h3 : (m : ℤ) ≠ m + 1 := by omega
    have h4 : m - 1 ∉ ({m, m + 1} : Finset ℤ) := by simp [h1, h2] <;> omega
    have h5 : m ∉ ({m + 1} : Finset ℤ) := by simp [h3] <;> omega
    calc S.card
      = (insert (m - 1) ({m, m + 1} : Finset ℤ)).card := by simp [S] <;> rfl
    _ = ({m, m + 1} : Finset ℤ).card + 1 := Finset.card_insert_of_notMem h4
    _ = (insert m ({m + 1} : Finset ℤ)).card + 1 := by rfl
    _ = ({m + 1} : Finset ℤ).card + 1 + 1 := by rw [Finset.card_insert_of_notMem h5]
    _ = 1 + 1 + 1 := by simp
    _ = 3 := by norm_num
  refine ⟨S, by rw [hS3] <;> norm_num, fun k hk => ?_⟩
  rcases hk with ⟨y, hy_cube, hy_ball⟩
  have h2 : δ * (k : ℝ) ≤ y := hy_cube.1
  have h3 : y < δ * ((k : ℝ) + 1) := hy_cube.2
  have h4 : x - δ ≤ y := hy_ball.1
  have h5 : y ≤ x + δ := hy_ball.2
  have h_upp : (k : ℝ) ≤ x / δ + 1 := by
    have h7 : δ * (k : ℝ) ≤ x + δ := by linarith
    have h8 : (k : ℝ) ≤ (x + δ) / δ := by
      calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x + δ) / δ := by gcongr
    have h9 : (x + δ) / δ = x / δ + 1 := by
      field_simp [hδ.ne'] <;> ring
    rw [h9] at h8; exact h8
  have h_low : x / δ - 2 < (k : ℝ) := by
    have h10 : x - δ < δ * ((k : ℝ) + 1) := by linarith
    have h11 : (x - δ) / δ < ((k : ℝ) + 1) := by
      calc (x - δ) / δ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
        _ = ((k : ℝ) + 1) := by field_simp [hδ.ne'] <;> ring
    have h12 : (x - δ) / δ = x / δ - 1 := by
      field_simp [hδ.ne'] <;> ring
    rw [h12] at h11; linarith
  have h13 : k ≤ m + 1 := by
    have h14 : (m : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h15 : x / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h131 : (k : ℝ) < (m : ℝ) + 2 := by linarith
    have h132 : k < m + 2 := by exact_mod_cast h131
    omega
  have h16 : m - 1 ≤ k := by
    have h17 : (m : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h18 : x / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h161 : (m : ℝ) - 2 < (k : ℝ) := by linarith
    have h162 : m - 2 < k := by exact_mod_cast h161
    omega
  simp only [S, Finset.mem_insert, Finset.mem_singleton] <;> omega

/-! ### Grid snapping helpers -/

/-- Any subset of the δ-grid inside a closed δ-ball is contained in a Finset of size ≤ 3. -/
lemma grid_ball_bound3 (δ : ℝ) (hδ : 0 < δ) (c : ℝ)
    {X : Set ℝ} (hX : X ⊆ productLikeIntegerGrid δ) :
    ∃ (s : Finset ℝ), (X ∩ Metric.closedBall c δ) ⊆ (s : Set ℝ) ∧ s.card ≤ 3 := by
  let m : ℤ := ⌊c / δ⌋
  let idx : Finset ℤ := Finset.Icc (m - 1) (m + 1)
  let s : Finset ℝ := idx.image (fun k : ℤ => δ * (k : ℝ))
  have h1 : ∀ x ∈ X ∩ Metric.closedBall c δ, x ∈ (s : Set ℝ) := by
    intro x hx
    have hxk : x ∈ productLikeIntegerGrid δ := hX hx.1
    rcases hxk with ⟨k, rfl⟩
    have hball : dist (δ * (k : ℝ)) c ≤ δ := hx.2
    have habs : |δ * (k : ℝ) - c| ≤ δ := by simpa [Real.dist_eq] using hball
    have h3 : c - δ ≤ δ * (k : ℝ) := by linarith [(abs_le.mp habs).1]
    have h4 : δ * (k : ℝ) ≤ c + δ := by linarith [(abs_le.mp habs).2]
    have h5 : (m : ℝ) - 1 ≤ (k : ℝ) := by
      have h6 : (m : ℝ) ≤ c / δ := Int.floor_le _
      calc (m : ℝ) - 1
        ≤ c / δ - 1 := by linarith
      _ = (c - δ) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (δ * (k : ℝ)) / δ := by gcongr
      _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
    have h7 : (k : ℝ) < (m : ℝ) + 2 := by
      have h8 : c / δ < (m : ℝ) + 1 := Int.lt_floor_add_one _
      calc (k : ℝ)
        = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (c + δ) / δ := by gcongr
      _ = c / δ + 1 := by field_simp [hδ.ne'] <;> ring
      _ < (m : ℝ) + 2 := by linarith
    have h9 : m - 1 ≤ k := by exact_mod_cast h5
    have h10 : k ≤ m + 1 := by
      have h11 : k < m + 2 := by exact_mod_cast h7
      omega
    have h12 : k ∈ idx := Finset.mem_Icc.mpr ⟨h9, h10⟩
    exact Finset.mem_image.mpr ⟨k, h12, rfl⟩
  have h_sub : (X ∩ Metric.closedBall c δ) ⊆ (s : Set ℝ) := h1
  have h_scard : s.card ≤ 3 := by
    have h : s.card ≤ idx.card := Finset.card_image_le
    have h2 : idx.card = 3 := by simp [idx] <;> omega
    rw [h2] at h; exact h
  exact ⟨s, h_sub, h_scard⟩

/-- Any subset of the δ-grid inside a closed 2δ-ball is contained in a Finset of size ≤ 5. -/
lemma grid_ball_bound5 (δ : ℝ) (hδ : 0 < δ) (c : ℝ)
    {X : Set ℝ} (hX : X ⊆ productLikeIntegerGrid δ) :
    ∃ (s : Finset ℝ), (X ∩ Metric.closedBall c (2 * δ)) ⊆ (s : Set ℝ) ∧ s.card ≤ 5 := by
  let m : ℤ := ⌊c / δ⌋
  let idx : Finset ℤ := Finset.Icc (m - 2) (m + 2)
  let s : Finset ℝ := idx.image (fun k : ℤ => δ * (k : ℝ))
  have h1 : ∀ x ∈ X ∩ Metric.closedBall c (2 * δ), x ∈ (s : Set ℝ) := by
    intro x hx
    have hxk : x ∈ productLikeIntegerGrid δ := hX hx.1
    rcases hxk with ⟨k, rfl⟩
    have hball : dist (δ * (k : ℝ)) c ≤ 2 * δ := hx.2
    have habs : |δ * (k : ℝ) - c| ≤ 2 * δ := by simpa [Real.dist_eq] using hball
    have h3 : c - 2 * δ ≤ δ * (k : ℝ) := by linarith [(abs_le.mp habs).1]
    have h4 : δ * (k : ℝ) ≤ c + 2 * δ := by linarith [(abs_le.mp habs).2]
    have h5 : (m : ℝ) - 2 ≤ (k : ℝ) := by
      have h6 : (m : ℝ) ≤ c / δ := Int.floor_le _
      calc (m : ℝ) - 2
        ≤ c / δ - 2 := by linarith
      _ = (c - 2 * δ) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (δ * (k : ℝ)) / δ := by gcongr
      _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
    have h7 : (k : ℝ) < (m : ℝ) + 3 := by
      have h8 : c / δ < (m : ℝ) + 1 := Int.lt_floor_add_one _
      calc (k : ℝ)
        = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (c + 2 * δ) / δ := by gcongr
      _ = c / δ + 2 := by field_simp [hδ.ne'] <;> ring
      _ < (m : ℝ) + 3 := by linarith
    have h9 : m - 2 ≤ k := by exact_mod_cast h5
    have h10 : k ≤ m + 2 := by
      have h11 : k < m + 3 := by exact_mod_cast h7
      omega
    have h12 : k ∈ idx := Finset.mem_Icc.mpr ⟨h9, h10⟩
    exact Finset.mem_image.mpr ⟨k, h12, rfl⟩
  have h_sub : (X ∩ Metric.closedBall c (2 * δ)) ⊆ (s : Set ℝ) := h1
  have h_scard : s.card ≤ 5 := by
    have h : s.card ≤ idx.card := Finset.card_image_le
    have h2 : idx.card = 5 := by simp [idx] <;> omega
    rw [h2] at h; exact h
  exact ⟨s, h_sub, h_scard⟩

/-- productLikeUnitGrid is finite. -/
lemma unitGrid_finite (δ : ℝ) (hδ : 0 < δ) : (productLikeUnitGrid δ).Finite := by
  let N : ℤ := ⌊1 / δ⌋
  let idx : Finset ℤ := Finset.Icc 0 N
  let s : Finset ℝ := idx.image (fun k : ℤ => δ * (k : ℝ))
  have h1 : productLikeUnitGrid δ ⊆ (s : Set ℝ) := by
    intro x hx
    have h2 : x ∈ productLikeIntegerGrid δ := hx.1
    have h3 : 0 ≤ x := hx.2.1
    have h4 : x ≤ 1 := hx.2.2
    rcases h2 with ⟨k, rfl⟩
    have h5 : 0 ≤ k := by
      have h6 : 0 ≤ δ * (k : ℝ) := h3
      have h7 : 0 ≤ (k : ℝ) := by nlinarith
      exact_mod_cast h7
    have h8 : k ≤ N := by
      have h9 : δ * (k : ℝ) ≤ 1 := h4
      have h10 : (k : ℝ) ≤ 1 / δ := by
        calc (k : ℝ)
          = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ 1 / δ := by gcongr
      exact Int.le_floor.mpr (by linarith)
    have h11 : k ∈ idx := Finset.mem_Icc.mpr ⟨h5, h8⟩
    exact Finset.mem_image.mpr ⟨k, h11, rfl⟩
  exact Set.Finite.subset (Finset.finite_toSet s) h1

/-- Snap a point in [0,1] to the δ-grid. -/
lemma snap_to_grid_in_unit (δ : ℝ) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1) :
    ∃ (g : ℝ), g ∈ productLikeUnitGrid δ ∧ |a - g| ≤ δ := by
  let k : ℤ := ⌊a / δ⌋
  let g : ℝ := δ * (k : ℝ)
  have h1 : g ∈ productLikeIntegerGrid δ := ⟨k, rfl⟩
  have h2 : 0 ≤ g := by
    have h3 : 0 ≤ a / δ := by positivity
    have h4 : 0 ≤ k := Int.floor_nonneg.mpr h3
    have h5 : 0 ≤ (k : ℝ) := by exact_mod_cast h4
    positivity
  have h5 : g ≤ a := by
    have h6 : (k : ℝ) ≤ a / δ := Int.floor_le _
    have h7 : δ * (k : ℝ) ≤ δ * (a / δ) := by gcongr
    have h8 : δ * (a / δ) = a := by field_simp [hδ.ne'] <;> ring
    linarith
  have h6 : g ≤ 1 := by linarith
  have h7 : a - g < δ := by
    have h8 : a / δ < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have h9 : a < δ * ((k : ℝ) + 1) := by
      have h10 : a = δ * (a / δ) := by field_simp [hδ.ne'] <;> ring
      rw [h10]
      gcongr <;> linarith
    have h11 : δ * ((k : ℝ) + 1) = g + δ := by simp [g] <;> ring
    linarith
  have h9 : 0 ≤ a - g := by linarith
  have h10 : |a - g| ≤ δ := by
    rw [abs_of_nonneg h9]
    linarith
  exact ⟨g, ⟨h1, ⟨h2, h6⟩⟩, h10⟩

/-- Bounded subset of ℝ has finite covering number. -/
lemma real_bounded_cov_finite {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_sub : A ⊆ Set.Icc (0 : ℝ) 1) :
    Metric.externalCoveringNumber δ.toNNReal A < ⊤ := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hne : δ.toNNReal ≠ 0 := by
    have h : (δ.toNNReal : ℝ) = δ := by
      rw [Real.coe_toNNReal] <;> linarith
    have h' : 0 < (δ.toNNReal : ℝ) := by rw [h]; exact hδ
    have hpos : 0 < δ.toNNReal := by exact_mod_cast h'
    exact hpos.ne'
  have hfin : ∃ (N : Set ℝ), N ⊆ Set.Icc (0 : ℝ) 1 ∧ N.Finite ∧ Metric.IsCover δ.toNNReal (Set.Icc (0 : ℝ) 1) N :=
    Metric.exists_finite_isCover_of_isCompact hne hcompact
  rcases hfin with ⟨N, _, hNfin, hNcover⟩
  have hcoverA : Metric.IsCover δ.toNNReal A N := hNcover.anti hA_sub
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ N.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcoverA
  have h2 : N.encard < ⊤ := Set.Finite.encard_lt_top hNfin
  exact h1.trans_lt h2

/-- Finite set covering number ≤ cardinality. -/
lemma finite_set_cov_le_card {δ : ℝ} (hδ : 0 < δ) {G : Set ℝ} (hG_fin : G.Finite) :
    Metric.externalCoveringNumber δ.toNNReal G ≤ (↑hG_fin.toFinset.card : ENNReal) := by
  have hGcover : Metric.IsCover δ.toNNReal G G := by
    intro g hg
    exact ⟨g, hg, by simp [edist_dist, hδ.le]⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal G ≤ G.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hGcover
  have h1' : (Metric.externalCoveringNumber δ.toNNReal G : ENNReal) ≤ (G.encard : ENNReal) := by exact_mod_cast h1
  have h2 : (G.encard : ENNReal) = (↑hG_fin.toFinset.card : ENNReal) := by
    have h3 : G.encard = ↑G.ncard := Set.Finite.encard_eq_coe hG_fin
    have h4 : G.ncard = hG_fin.toFinset.card := by exact Set.ncard_eq_toFinset_card G hG_fin
    rw [h3, h4] <;> norm_cast
  rw [h2] at h1'
  exact h1'

/-- Convert edist bound to dist bound. -/
lemma edist_bound_to_dist {x y : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : edist x y ≤ ↑δ.toNNReal) : dist x y ≤ δ := by
  have h_eq1 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist x y
  have h_eq2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
  rw [h_eq1, h_eq2] at h
  have hpos : 0 ≤ dist x y := by positivity
  have h_iff : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal δ ↔ dist x y ≤ δ :=
    ENNReal.ofReal_le_ofReal_iff (by linarith)
  exact h_iff.mp h

/-- Grid set cardinality ≤ 3 * covering number. -/
lemma grid_set_card_le_3cov {δ : ℝ} (hδ : 0 < δ) {G : Set ℝ}
    (hG_sub : G ⊆ productLikeIntegerGrid δ) (hG_fin : G.Finite) :
    (↑hG_fin.toFinset.card : ENNReal) ≤ (3 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal G : ENNReal) := by
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal G = ⊤
  · rw [h_top] <;> simp
  · have h_lt_top : Metric.externalCoveringNumber δ.toNNReal G < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_lt_top with ⟨D, hDcover, hD_eq⟩
    have hD_fin : D.Finite := Set.encard_ne_top_iff.mp (by rw [hD_eq] <;> exact h_top)
    let D_fin := hD_fin.toFinset
    choose G_c hG_subset hG_card using fun c : ℝ => grid_ball_bound3 δ hδ c (hX := hG_sub)
    have h1 : G ⊆ ⋃ c ∈ D_fin, (G_c c : Set ℝ) := by
      intro g hg
      have hcovered : ∃ (c : ℝ), c ∈ D ∧ edist g c ≤ ↑δ.toNNReal := hDcover hg
      rcases hcovered with ⟨c, hcD, hedistance⟩
      have hdist : dist g c ≤ δ := edist_bound_to_dist hδ hedistance
      have hball : g ∈ Metric.closedBall c δ := by simpa [Metric.mem_closedBall] using hdist
      have hc_in : c ∈ D_fin := by simpa [D_fin] using hcD
      have hg_in : g ∈ (G_c c : Set ℝ) := hG_subset c ⟨hg, hball⟩
      simpa [Finset.mem_biUnion] using ⟨c, hc_in, hg_in⟩
    have h2 : hG_fin.toFinset ⊆ D_fin.biUnion G_c := by simpa [hG_fin] using h1
    have h3 : hG_fin.toFinset.card ≤ (D_fin.biUnion G_c).card := Finset.card_le_card h2
    have h4 : (D_fin.biUnion G_c).card ≤ ∑ c ∈ D_fin, (G_c c).card := Finset.card_biUnion_le
    have h5 : ∀ c ∈ D_fin, (G_c c).card ≤ 3 := fun c _ => hG_card c
    have h6 : ∑ c ∈ D_fin, (G_c c).card ≤ D_fin.card * 3 := by
      calc ∑ c ∈ D_fin, (G_c c).card
        ≤ ∑ c ∈ D_fin, 3 := Finset.sum_le_sum h5
      _ = D_fin.card * 3 := by simp [Finset.sum_const] <;> ring
    have h7 : hG_fin.toFinset.card ≤ D_fin.card * 3 := h3.trans (h4.trans h6)
    have h10 : D.encard = ↑D_fin.card := by
      have h12 : D.encard = ↑D.ncard := Set.Finite.encard_eq_coe hD_fin
      have h13 : D.ncard = D_fin.card := by simp [D_fin, hD_fin.coe_toFinset] <;> exact Set.ncard_eq_toFinset_card D hD_fin
      rw [h12, h13]
    have h11 : (↑D_fin.card : ENNReal) = ↑(D.encard : ENNReal) := by exact_mod_cast h10.symm
    have h12' : (↑(D.encard : ENNReal) : ENNReal) = (Metric.externalCoveringNumber δ.toNNReal G : ENNReal) := by
      exact_mod_cast hD_eq
    calc (↑hG_fin.toFinset.card : ENNReal)
      ≤ (↑(D_fin.card * 3) : ENNReal) := by exact_mod_cast h7
    _ = 3 * (↑D_fin.card : ENNReal) := by simp [mul_comm] <;> ring
    _ = 3 * (↑(D.encard : ENNReal) : ENNReal) := by rw [h11]
    _ = 3 * (Metric.externalCoveringNumber δ.toNNReal G : ENNReal) := by rw [h12']

/-- Grid points near a set — cardinality ≤ 5 * cov(S). -/
lemma grid_near_set_card_le_5cov {δ : ℝ} (hδ : 0 < δ)
    {G S : Set ℝ} (hG_sub : G ⊆ productLikeIntegerGrid δ) (hG_fin : G.Finite)
    (hS_cov_lt_top : Metric.externalCoveringNumber δ.toNNReal S < ⊤)
    (h_near : ∀ g ∈ G, ∃ s ∈ S, |g - s| ≤ δ) :
    (↑hG_fin.toFinset.card : ENNReal) ≤ (5 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
  rcases exists_external_cover_eq hS_cov_lt_top with ⟨D, hDcover, hD_eq⟩
  have hD_fin : D.Finite := Set.encard_ne_top_iff.mp (by rw [hD_eq] <;> exact hS_cov_lt_top.ne)
  let D_fin := hD_fin.toFinset
  choose G_c hG_subset hG_card using fun c : ℝ => grid_ball_bound5 δ hδ c (hX := hG_sub)
  have h1 : G ⊆ ⋃ c ∈ D_fin, (G_c c : Set ℝ) := by
    intro g hg
    rcases h_near g hg with ⟨s, hsS, hdist_gs⟩
    have hcovered : ∃ (c : ℝ), c ∈ D ∧ edist s c ≤ ↑δ.toNNReal := hDcover hsS
    rcases hcovered with ⟨c, hcD, hedistance⟩
    have hdist_sc : dist s c ≤ δ := edist_bound_to_dist hδ hedistance
    have hdist_gc : dist g c ≤ 2 * δ := by
      calc dist g c
        ≤ dist g s + dist s c := dist_triangle g s c
      _ = |g - s| + dist s c := by rw [Real.dist_eq]
      _ ≤ δ + δ := by linarith
      _ = 2 * δ := by ring
    have hball : g ∈ Metric.closedBall c (2 * δ) := by simpa [Metric.mem_closedBall] using hdist_gc
    have hc_in : c ∈ D_fin := by simpa [D_fin] using hcD
    have hg_in : g ∈ (G_c c : Set ℝ) := hG_subset c ⟨hg, hball⟩
    simpa [Finset.mem_biUnion] using ⟨c, hc_in, hg_in⟩
  have h2 : hG_fin.toFinset ⊆ D_fin.biUnion G_c := by simpa [hG_fin] using h1
  have h3 : hG_fin.toFinset.card ≤ (D_fin.biUnion G_c).card := Finset.card_le_card h2
  have h4 : (D_fin.biUnion G_c).card ≤ ∑ c ∈ D_fin, (G_c c).card := Finset.card_biUnion_le
  have h5 : ∀ c ∈ D_fin, (G_c c).card ≤ 5 := fun c _ => hG_card c
  have h6 : ∑ c ∈ D_fin, (G_c c).card ≤ D_fin.card * 5 := by
    calc ∑ c ∈ D_fin, (G_c c).card
      ≤ ∑ c ∈ D_fin, 5 := Finset.sum_le_sum h5
    _ = D_fin.card * 5 := by simp [Finset.sum_const] <;> ring
  have h7 : hG_fin.toFinset.card ≤ D_fin.card * 5 := h3.trans (h4.trans h6)
  have h10 : D.encard = ↑D_fin.card := by
    have h12 : D.encard = ↑D.ncard := Set.Finite.encard_eq_coe hD_fin
    have h13 : D.ncard = D_fin.card := by simp [D_fin, hD_fin.coe_toFinset] <;> exact Set.ncard_eq_toFinset_card D hD_fin
    rw [h12, h13]
  have h11 : (↑D_fin.card : ENNReal) = ↑(D.encard : ENNReal) := by exact_mod_cast h10.symm
  have h12' : (↑(D.encard : ENNReal) : ENNReal) = (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
    exact_mod_cast hD_eq
  calc (↑hG_fin.toFinset.card : ENNReal)
    ≤ (↑(D_fin.card * 5) : ENNReal) := by exact_mod_cast h7
  _ = 5 * (↑D_fin.card : ENNReal) := by simp [mul_comm] <;> ring
  _ = 5 * (↑(D.encard : ENNReal) : ENNReal) := by rw [h11]
  _ = 5 * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by rw [h12']

/-- IsDeltaSSet preserved under isometry equivalence. -/
lemma isDeltaSSet_image_isometryEquiv {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ᵢ Y) {δ s C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C (e '' P) := by
  have hne : (e '' P).Nonempty := h.1.image e
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs_nonneg : 0 ≤ s := h.2.2.2.1
  have h_main : ∀ (x : X) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) :=
    h.2.2.2.2
  refine ⟨hne, hδ_pos, hC_pos, hs_nonneg, ?_⟩
  intro y r hr
  have h1 : (e '' P) ∩ Metric.closedBall y r = e '' (P ∩ Metric.closedBall (e.symm y) r) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hdist⟩
      have h2 : dist x (e.symm y) ≤ r := by
        have h3 : dist (e x) y ≤ r := hdist
        have h4 : dist (e x) (e (e.symm y)) = dist x (e.symm y) := e.dist_eq x (e.symm y)
        have h5 : e (e.symm y) = y := e.apply_symm_apply y
        rw [h5] at h4
        rw [←h4]
        exact h3
      exact ⟨x, ⟨hx, h2⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hdist⟩, rfl⟩
      have h2 : dist (e x) y ≤ r := by
        have h3 : dist x (e.symm y) ≤ r := hdist
        have h4 : dist (e x) (e (e.symm y)) = dist x (e.symm y) := e.dist_eq x (e.symm y)
        have h5 : e (e.symm y) = y := e.apply_symm_apply y
        rw [h5] at h4
        rw [h4]
        exact h3
      exact ⟨⟨x, hx, rfl⟩, h2⟩
  rw [h1]
  have hcov1 : Metric.externalCoveringNumber δ.toNNReal (e '' (P ∩ Metric.closedBall (e.symm y) r)) =
      Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (e.symm y) r) :=
    externalCoveringNumber_image_isometryEquiv e
  have hcov2 : Metric.externalCoveringNumber δ.toNNReal (e '' P) =
      Metric.externalCoveringNumber δ.toNNReal P :=
    externalCoveringNumber_image_isometryEquiv e
  rw [hcov1, hcov2]
  exact h_main (e.symm y) r hr

/-- A bounded 1D S-set can be snapped to the δ-grid in [0,1] to produce
a `productLikeUnitGrid δ` subset that is an SC-set with constant 100*C. -/
lemma sset_to_grid_scset {δ s C : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 < C)
    {A : Set ℝ} (hA_sub : A ⊆ Set.Icc (0 : ℝ) 1)
    (hA_bdd : Bornology.IsBounded A)
    (hA_nonempty : A.Nonempty)
    (hA : IsDeltaSSet δ s C A) :
    ∃ (A_grid : Set ℝ),
      A_grid ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s (C * 100) A_grid ∧
      (Metric.externalCoveringNumber δ.toNNReal A_grid : ENNReal) ≥
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) / 100 ∧
      (∀ g ∈ A_grid, ∃ a ∈ A, |g - a| ≤ δ) := by
  exact DiscretisedFurstenbergEstimate.GridSnap.sset_to_grid_scset hδ hδ_dyadic hs hs1 hC hA_sub hA_bdd hA_nonempty hA
