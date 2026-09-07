import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.SliceCovering
import MyLeanRepo.Kakeya.Assouad.LargeSlope.GlobalADVolumeBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperGlobalADVolumeUpper
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CleanedTwistedProjectionUpper
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Core AD+Fubini volume bound for Node 7

Given a PureWZ2LargeSlopeConfiguration, prove
`volume (twistedProjection slope '' shading.union) ≤ 24 * delta^(sigma-loss)`.

Uses the paper AD condition directly on each horizontal slice, then Fubini.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

-- ============================================================================
-- Helper: inner product with global grain direction
-- ============================================================================

private lemma global_grain_inner (m : ℝ) (p : Point3) :
    inner ℝ p (globalGrainDirection m) = p 0 + m * p 1 := by
  have h1 : inner ℝ p (globalGrainDirection m) =
      inner ℝ p (EuclideanSpace.single (0 : Fin 3) 1 + m • EuclideanSpace.single (1 : Fin 3) 1) := by
    rfl
  rw [h1, inner_add_right, inner_smul_right]
  have h2 : inner ℝ p (EuclideanSpace.single (0 : Fin 3) 1) = p 0 := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  have h3 : inner ℝ p (EuclideanSpace.single (1 : Fin 3) 1) = p 1 := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  rw [h2, h3]

-- ============================================================================
-- Slice identity
-- ============================================================================

/-- The slice of the twisted projection at height z equals the scalar
projection of the horizontal slice onto the grain direction. -/
lemma twistedProjection_slice_identity
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction} {z : ℝ} :
    sliceAt (twistedProjection f '' Y.union) z =
    scalarProjection (globalGrainDirection (f z)) (horizontalSlice Y.union z) := by
  ext x
  simp only [sliceAt, Set.mem_image, scalarProjection, horizontalSlice]
  constructor
  · rintro ⟨p, ⟨hp, hpt⟩, rfl⟩
    rcases hp with ⟨q, hq, rfl⟩
    have hz : q 2 = z := by simpa using hpt
    have hhoriz : (twistedProjection f q) 0 = q 0 + f z * q 1 := by
      simp [twistedProjection, hz]
    have hinner : inner ℝ q (globalGrainDirection (f z)) = q 0 + f z * q 1 :=
      global_grain_inner (f z) q
    exact ⟨q, ⟨hq, hz⟩, by rw [hhoriz, hinner]⟩
  · rintro ⟨q, ⟨hq, hz⟩, rfl⟩
    let p := twistedProjection f q
    have hp_in : p ∈ twistedProjection f '' Y.union := ⟨q, hq, rfl⟩
    have hbs : p 1 = q 2 := by
      simp [p, twistedProjection]
    have hhoriz : p 0 = inner ℝ q (globalGrainDirection (f z)) := by
      have h1 : p 0 = q 0 + f z * q 1 := by
        simp [p, twistedProjection, hz]
      have h2 : inner ℝ q (globalGrainDirection (f z)) = q 0 + f z * q 1 :=
        global_grain_inner (f z) q
      rw [h1, h2]
    exact ⟨p, ⟨hp_in, by rw [hbs, hz]⟩, hhoriz⟩

-- ============================================================================
-- Boundedness: paper shading carriers are in axisBox 2 2 2
-- ============================================================================

lemma paper_shading_in_axisBox
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : WZ1PaperTubeShading F} {p : Point3} (hp : p ∈ Y.union) :
    p ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
  rcases (Set.mem_setOf_eq.mp hp) with ⟨i, hi⟩
  have h_carrier : p ∈ Y.carrier i := hi
  have h_sub : Y.carrier i ⊆ ((wz1PaperBodyFamily F).body i).carrier :=
    Y.subset_body i
  have h_in : p ∈ ((wz1PaperBodyFamily F).body i).carrier := h_sub h_carrier
  have h_final : p ∈ wz1PaperTubeCarrier (F.tube i) := by
    simpa [wz1PaperBodyFamily] using h_in
  exact h_final.2

-- ============================================================================
-- Z-dependent boundedness of scalar projection
-- ============================================================================

/-- For nonsingular f with f 0 = 0, `|f z| ≤ 2 * |z|` on `[-1,1]`. -/
lemma nonsingular_f_linear_bound {f : SlopeFunction}
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0) {z : ℝ}
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |f z| ≤ 2 * |z| := by
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖deriv f x‖ ≤ 2 := by
    intro x hx
    have h : |deriv f x| ≤ 2 := (h_ns x hx).2.1
    simpa using h
  have h_conv : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc (-1 : ℝ) 1
  have h0_in : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have h_diff_on : ∀ x ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ f x := by
    intro x hx
    have h1 : 1 ≤ |deriv f x| := (h_ns x hx).1
    have h2 : deriv f x ≠ 0 := by
      have h3 : 0 < |deriv f x| := by linarith
      have h4 : |deriv f x| ≠ 0 := ne_of_gt h3
      exact abs_ne_zero.mp h4
    by_cases h4 : DifferentiableAt ℝ f x
    · exact h4
    · have h5 : deriv f x = 0 := deriv_zero_of_not_differentiableAt h4
      contradiction
  have hft : ‖f z - f 0‖ ≤ 2 * ‖z - (0 : ℝ)‖ :=
    h_conv.norm_image_sub_le_of_norm_deriv_le h_diff_on hderiv h0_in hz
  have h_abs : |f z - f 0| ≤ 2 * |z| := by
    have h9 : ‖f z - f 0‖ = |f z - f 0| := by simp
    have h10 : ‖z - (0 : ℝ)‖ = |z| := by simp
    rw [h9, h10] at hft
    exact hft
  have h0' : f 0 = 0 := h0
  have h11 : f z = f z - f 0 := by rw [h0'] <;> ring
  rw [h11]
  exact h_abs

/-- The scalar projection of the horizontal slice at height z is contained in
`[-(1+2|z|), 1+2|z|]`. -/
lemma paper_slice_bounded_z_dependent
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (hf_nonsing : f.IsNonsingular) (hf_zero : f 0 = 0)
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection (globalGrainDirection (f z)) (horizontalSlice Y.union z) ⊆
    Set.Icc (-(1 + 2 * |z|)) (1 + 2 * |z|) := by
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  have hp_box : p ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    paper_shading_in_axisBox hp.1
  have h0 : |p 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hp_box.1
  have h1 : |p 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hp_box.2.1
  have hfz : |f z| ≤ 2 * |z| := nonsingular_f_linear_bound hf_nonsing hf_zero hz
  have h_eq : inner ℝ p (globalGrainDirection (f z)) = p 0 + f z * p 1 :=
    global_grain_inner (f z) p
  have h4 : |p 0| + |f z| * |p 1| ≤ 1 + 2 * |z| := by
    have h5 : 0 ≤ 2 * |z| := by positivity
    have h6 : |f z| * |p 1| ≤ (2 * |z|) * 1 := mul_le_mul hfz h1 (abs_nonneg _) h5
    have h7 : |p 0| ≤ 1 := h0
    linarith
  have h_main : |inner ℝ p (globalGrainDirection (f z))| ≤ 1 + 2 * |z| := by
    rw [h_eq]
    calc |p 0 + f z * p 1|
      ≤ |p 0| + |f z * p 1| := abs_add_le _ _
    _ = |p 0| + |f z| * |p 1| := by rw [abs_mul]
    _ ≤ 1 + 2 * |z| := h4
  have h_abs : |inner ℝ p (globalGrainDirection (f z))| ≤ 1 + 2 * |z| := h_main
  have h_left : -(1 + 2 * |z|) ≤ inner ℝ p (globalGrainDirection (f z)) := by
    linarith [abs_le.mp h_abs]
  have h_right : inner ℝ p (globalGrainDirection (f z)) ≤ 1 + 2 * |z| := by
    linarith [abs_le.mp h_abs]
  exact ⟨h_left, h_right⟩

-- ============================================================================
-- Volume bound from paper AD condition on a bounded interval
-- ============================================================================

/-- Given `PureWZ2PaperADSet1 E δ α C` and `E ⊆ [-L,L]`, bound
`volume E ≤ 2 * C * (2L)^α * δ^(1-α)`. -/
lemma paper_ad_volume_on_interval
    {E : Set ℝ} {δ α L : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 E δ α C)
    (hδ : 0 < δ) (hL_pos : 0 < L) (hδ_le : δ ≤ 2 * L)
    (hE : E ⊆ Set.Icc (-L) L) :
    volume E ≤
    2 * C * Kakeya.realRpowENN (2 * L) α * Kakeya.realRpowENN δ (1 - α) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have h2L_pos : 0 < 2 * L := by linarith
  have hcover' : (↑(Metric.externalCoveringNumber ⟨δ, hδ_pos.le⟩ E) : ENNReal) ≤
      C * Kakeya.realRpowENN (2 * L / δ) α := by
    have h_int : Set.Icc (-L) (-L + 2 * L) = Set.Icc (-L) L := by
      have h_eq : -L + 2 * L = L := by ring
      rw [h_eq]
    have hE_int : E ∩ Set.Icc (-L) (-L + 2 * L) = E := by
      rw [h_int]
      exact Set.inter_eq_left.mpr hE
    have h := hcover δ hδ_pos.le le_rfl (-L) (2 * L) (by linarith)
    rw [hE_int] at h
    exact h
  have hN_top : (C * Kakeya.realRpowENN (2 * L / δ) α) ≠ ⊤ :=
    ENNReal.mul_ne_top hC_top (by simp [Kakeya.realRpowENN])
  have hvol : volume E ≤ C * Kakeya.realRpowENN (2 * L / δ) α * ENNReal.ofReal (2 * δ) :=
    volume_le_externalCoveringNumber_mul_two_delta hδ_pos hN_top hcover'

  -- Real arithmetic identity
  have h1 : Real.rpow (2 * L / δ) α =
      Real.rpow (2 * L) α / Real.rpow δ α :=
    Real.div_rpow (by linarith) (by linarith) α
  have h2 : Real.rpow δ (1 - α) = δ / Real.rpow δ α := by
    have hsub : Real.rpow δ (1 - α) = Real.rpow δ 1 / Real.rpow δ α :=
      Real.rpow_sub (by linarith) 1 α
    have h3 : Real.rpow δ 1 = δ := by simp
    rw [hsub, h3]
  have h4 : 0 < Real.rpow δ α := Real.rpow_pos_of_pos hδ α
  have h_real : Real.rpow (2 * L / δ) α * (2 * δ) =
      2 * Real.rpow (2 * L) α * Real.rpow δ (1 - α) := by
    rw [h1, h2]
    field_simp [h4.ne'] <;> ring

  -- ENNReal lifting
  have hpos_a : 0 ≤ Real.rpow (2 * L / δ) α := Real.rpow_nonneg (by positivity) α
  have hpos_b : 0 ≤ (2 * δ) := by positivity
  have h_ofReal1 : ENNReal.ofReal (Real.rpow (2 * L / δ) α * (2 * δ)) =
      ENNReal.ofReal (Real.rpow (2 * L / δ) α) * ENNReal.ofReal (2 * δ) := by
    rw [ENNReal.ofReal_mul hpos_a]
  have hpos_c : 0 ≤ Real.rpow (2 * L) α := Real.rpow_nonneg (by positivity) α
  have hpos_d : 0 ≤ Real.rpow δ (1 - α) := Real.rpow_nonneg (by positivity) _
  have h_ofReal2 : ENNReal.ofReal (2 * Real.rpow (2 * L) α * Real.rpow δ (1 - α)) =
      2 * ENNReal.ofReal (Real.rpow (2 * L) α) * ENNReal.ofReal (Real.rpow δ (1 - α)) := by
    have h5 : 0 ≤ (2 : ℝ) := by positivity
    have h_step1 : ENNReal.ofReal (2 * Real.rpow (2 * L) α * Real.rpow δ (1 - α)) =
        ENNReal.ofReal (2 * Real.rpow (2 * L) α) * ENNReal.ofReal (Real.rpow δ (1 - α)) :=
      ENNReal.ofReal_mul (by positivity)
    have h_step2 : ENNReal.ofReal (2 * Real.rpow (2 * L) α) =
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (Real.rpow (2 * L) α) :=
      ENNReal.ofReal_mul h5
    rw [h_step1, h_step2]
    <;> simp [mul_assoc] <;> ring

  have hrpow : Kakeya.realRpowENN (2 * L / δ) α * ENNReal.ofReal (2 * δ) =
      2 * Kakeya.realRpowENN (2 * L) α * Kakeya.realRpowENN δ (1 - α) := by
    have h5 : Kakeya.realRpowENN (2 * L / δ) α = ENNReal.ofReal (Real.rpow (2 * L / δ) α) := by rfl
    rw [h5]
    rw [←h_ofReal1, h_real, h_ofReal2]
    <;> simp [Kakeya.realRpowENN, mul_assoc] <;> ring

  have hvol' : volume E ≤ C * (Kakeya.realRpowENN (2 * L / δ) α * ENNReal.ofReal (2 * δ)) := by
    simpa [mul_assoc] using hvol
  rw [hrpow] at hvol'
  have h_final : volume E ≤
      2 * C * Kakeya.realRpowENN (2 * L) α * Kakeya.realRpowENN δ (1 - α) := by
    convert hvol' using 1
    <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  exact h_final

-- ============================================================================
-- Sigma-compactness of cubical shading unions
-- ============================================================================

/-- Coordinate projection from a 3-tuple of integers. -/
private def cellCoord (cell : ℤ × ℤ × ℤ) : Fin 3 → ℤ :=
  ![cell.1, cell.2.1, cell.2.2]

/-- A closed inner approximation of a grid cube. -/
def gridCubeCompactCover (δ : ℝ) (cell : ℤ × ℤ × ℤ) (n : ℕ) : Set Point3 :=
  {p | ∀ i : Fin 3, (cellCoord cell i : ℝ) * δ ≤ p i ∧
       p i ≤ ((cellCoord cell i : ℝ) + 1) * δ - δ / (n + 2)}

/-- Each inner approximation box is compact. -/
lemma gridCubeCompactCover_compact
    {δ : ℝ} (hδ : 0 < δ) (cell : ℤ × ℤ × ℤ) (n : ℕ) :
    IsCompact (gridCubeCompactCover δ cell n) := by
  let a : Fin 3 → ℝ := fun i => (cellCoord cell i : ℝ) * δ
  let b : Fin 3 → ℝ := fun i => ((cellCoord cell i : ℝ) + 1) * δ - δ / (n + 2)
  have h_pos2 : (0 : ℝ) < (n + 2 : ℝ) := by exact_mod_cast (show 0 < n + 2 by omega)
  have h_div_nonneg : 0 ≤ δ / (n + 2 : ℝ) := by positivity
  have h_div_le : δ / (n + 2 : ℝ) ≤ δ := by
    have h1 : (1 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
    have h2 : δ / (n + 2 : ℝ) ≤ δ / (1 : ℝ) := by
      apply div_le_div_of_nonneg_left hδ.le
      <;> linarith
    simpa using h2
  have h_ab : ∀ i, a i ≤ b i := by
    intro i
    dsimp only [a, b]
    linarith
  let M : ℝ := |a 0| + δ + |a 1| + δ + |a 2| + δ
  have h_closed : IsClosed (gridCubeCompactCover δ cell n) := by
    have h1 : ∀ i : Fin 3, IsClosed {p : Point3 | a i ≤ p i} := by
      intro i
      have hci : Continuous (fun p : Point3 => p i) :=
        PiLp.continuous_apply 2 (fun x => ℝ) i
      exact isClosed_Ici.preimage hci
    have h2 : ∀ i : Fin 3, IsClosed {p : Point3 | p i ≤ b i} := by
      intro i
      have hci : Continuous (fun p : Point3 => p i) :=
        PiLp.continuous_apply 2 (fun x => ℝ) i
      exact isClosed_Iic.preimage hci
    have h3 : gridCubeCompactCover δ cell n =
        ⋂ i : Fin 3, ({p : Point3 | a i ≤ p i} ∩ {p : Point3 | p i ≤ b i}) := by
      ext q
      simp only [gridCubeCompactCover, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      <;> constructor <;> intro h <;> intro i <;> exact h i
    rw [h3]
    apply isClosed_iInter
    intro i
    exact (h1 i).inter (h2 i)
  have h_sub : gridCubeCompactCover δ cell n ⊆ Metric.closedBall (0 : Point3) M := by
    intro p hp
    have h5 : ∀ i : Fin 3, |p i| ≤ |a i| + δ := by
      intro i
      have h6 : a i ≤ p i := (hp i).1
      have h7 : p i ≤ b i := (hp i).2
      have h8 : p i ≤ a i + δ := by
        dsimp only [a, b] at h7
        linarith
      exact abs_le.mpr ⟨by linarith [neg_abs_le (a i)], by
        by_cases h9 : 0 ≤ a i
        · rw [abs_of_nonneg h9] <;> linarith
        · rw [abs_of_neg (by linarith)] <;> linarith⟩
    have h_norm2 : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
      have hsum : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> ring
      rw [hsum]
      have hnonneg : 0 ≤ (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
        exact add_nonneg (add_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))) (sq_nonneg (p 2))
      rw [Real.sq_sqrt hnonneg]
    have h_norm_le : ‖p‖ ≤ |p 0| + |p 1| + |p 2| := by
      have hsq : ‖p‖ ^ 2 ≤ (|p 0| + |p 1| + |p 2|) ^ 2 := by
        rw [h_norm2]
        have h1 : (|p 0| + |p 1| + |p 2|) ^ 2 =
            |p 0| ^ 2 + |p 1| ^ 2 + |p 2| ^ 2 +
            2 * (|p 0| * |p 1| + |p 0| * |p 2| + |p 1| * |p 2|) := by ring
        rw [h1]
        have h2 : |p 0| ^ 2 = (p 0) ^ 2 := by simp
        have h3 : |p 1| ^ 2 = (p 1) ^ 2 := by simp
        have h4 : |p 2| ^ 2 = (p 2) ^ 2 := by simp
        rw [h2, h3, h4]
        have h5 : 0 ≤ 2 * (|p 0| * |p 1| + |p 0| * |p 2| + |p 1| * |p 2|) := by positivity
        linarith
      have hpos1 : 0 ≤ ‖p‖ := by positivity
      have hpos2 : 0 ≤ |p 0| + |p 1| + |p 2| := by positivity
      nlinarith
    have h6 := h5 0
    have h7 := h5 1
    have h8 := h5 2
    have h9 : ‖p‖ ≤ M := by
      calc ‖p‖ ≤ |p 0| + |p 1| + |p 2| := h_norm_le
        _ ≤ (|a 0| + δ) + (|a 1| + δ) + (|a 2| + δ) := by linarith
        _ = M := by simp [M] <;> ring
    simpa [Metric.mem_closedBall] using h9
  have h_compact_ball : IsCompact (Metric.closedBall (0 : Point3) M) :=
    isCompact_closedBall 0 M
  exact h_compact_ball.of_isClosed_subset h_closed h_sub

/-- The grid cube is the countable union of its compact inner approximations. -/
lemma gridCubeCompactCover_cover
    {δ : ℝ} (hδ : 0 < δ) (cell : ℤ × ℤ × ℤ) :
    wz1PaperGridCube δ cell = ⋃ n : ℕ, gridCubeCompactCover δ cell n := by
  ext p
  have h_eq1 : p ∈ wz1PaperGridCube δ cell ↔
      (cell.1 : ℝ) * δ ≤ p 0 ∧ p 0 < ((cell.1 : ℝ) + 1) * δ ∧
      (cell.2.1 : ℝ) * δ ≤ p 1 ∧ p 1 < ((cell.2.1 : ℝ) + 1) * δ ∧
      (cell.2.2 : ℝ) * δ ≤ p 2 ∧ p 2 < ((cell.2.2 : ℝ) + 1) * δ := by
    rw [wz1PaperGridCube_eq_Ico hδ cell]
    <;> rfl
  have h_forall : (∀ i : Fin 3, (cellCoord cell i : ℝ) * δ ≤ p i ∧
        p i < ((cellCoord cell i : ℝ) + 1) * δ) ↔
      ((cell.1 : ℝ) * δ ≤ p 0 ∧ p 0 < ((cell.1 : ℝ) + 1) * δ ∧
       (cell.2.1 : ℝ) * δ ≤ p 1 ∧ p 1 < ((cell.2.1 : ℝ) + 1) * δ ∧
       (cell.2.2 : ℝ) * δ ≤ p 2 ∧ p 2 < ((cell.2.2 : ℝ) + 1) * δ) := by
    simp [cellCoord, Fin.forall_fin_succ]
    <;> tauto
  rw [h_eq1, ←h_forall]
  simp only [Set.mem_iUnion, gridCubeCompactCover, Set.mem_setOf_eq]
  constructor
  · intro h
    have hε0 : 0 < ((cellCoord cell 0 : ℝ) + 1) * δ - p 0 := by linarith [(h 0).2]
    have hε1 : 0 < ((cellCoord cell 1 : ℝ) + 1) * δ - p 1 := by linarith [(h 1).2]
    have hε2 : 0 < ((cellCoord cell 2 : ℝ) + 1) * δ - p 2 := by linarith [(h 2).2]
    let ε := min (min (((cellCoord cell 0 : ℝ) + 1) * δ - p 0)
        (((cellCoord cell 1 : ℝ) + 1) * δ - p 1))
        (((cellCoord cell 2 : ℝ) + 1) * δ - p 2)
    have hε_pos : 0 < ε := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (δ / ε)
    have hlt : δ / (n + 2 : ℝ) < ε := by
      have h5 : (n + 2 : ℝ) > δ / ε := by linarith
      calc δ / (n + 2 : ℝ)
        < δ / (δ / ε) := by gcongr
      _ = ε := by field_simp [hε_pos.ne'] <;> ring
    refine' ⟨n, _⟩
    intro i
    have h7 : ((cellCoord cell i : ℝ) + 1) * δ - p i ≥ ε := by
      fin_cases i <;> simp [ε] <;> linarith
    exact ⟨(h i).1, by linarith⟩
  · rintro ⟨n, hn⟩
    intro i
    have h := hn i
    have hpos : 0 < δ / (n + 2 : ℝ) := by positivity
    exact ⟨h.1, by linarith⟩

/-- A cubical shading union equals the finite union of its active grid cubes. -/
lemma cubicalUnion_eq_activeCells
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : WZ1PaperTubeShading F}
    (hcub : WZ1PaperIsCubicalShading Y) (hδ : 0 < δ) :
    Y.union = ⋃ cell ∈ (wz1PaperActiveCells Y hδ : Set (ℤ × ℤ × ℤ)),
        wz1PaperGridCube δ cell := by
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    set cell : ℤ × ℤ × ℤ := wz1PaperGridIndex δ p with hcell_def
    have h_grid_eq : gridIndex δ p = cell := by
      simp [hcell_def, wz1PaperGridIndex]
    have h_in : p ∈ wz1PaperGridCube δ cell := by
      simpa [wz1PaperGridCube] using h_grid_eq
    have hp_union : p ∈ Y.union := ⟨i, hi⟩
    have hp_box : p ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      paper_shading_in_axisBox hp_union
    have h_window : cell ∈ wz1PaperGridIndicesInWindow δ hδ :=
      paper_point_gridIndex_in_window hδ hp_box
    have h_nonempty : (Y.union ∩ wz1PaperGridCube δ cell).Nonempty :=
      ⟨p, ⟨hp_union, h_in⟩⟩
    have h_active : cell ∈ wz1PaperActiveCells Y hδ := by
      rw [mem_wz1PaperActiveCells (hscale := hδ)]
      exact ⟨h_window, h_nonempty⟩
    exact ⟨cell, h_active, h_in⟩
  · rintro ⟨cell, hcell, hpcube⟩
    have hcell' : cell ∈ wz1PaperActiveCells Y hδ := by exact_mod_cast hcell
    have h : Y.union ∩ wz1PaperGridCube δ cell = wz1PaperGridCube δ cell :=
      hcub.inter_activeCell_eq hδ hcell'
    have h' : p ∈ Y.union ∩ wz1PaperGridCube δ cell := by
      rw [h]
      exact hpcube
    exact h'.1

/-- The continuous image of a cubical shading union is Borel measurable,
because it is a countable union of compact sets. -/
lemma cubicalUnion_image_measurable
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (hcub : WZ1PaperIsCubicalShading Y) (hδ : 0 < δ) :
    MeasurableSet (twistedProjection f '' Y.union) := by
  let activeCells : Set (ℤ × ℤ × ℤ) := ↑(wz1PaperActiveCells Y hδ)
  have h_fin : Set.Countable activeCells := (Finset.finite_toSet _).countable
  have h_union_eq : Y.union = ⋃ cell ∈ activeCells, wz1PaperGridCube δ cell :=
    cubicalUnion_eq_activeCells hcub hδ
  let C : (ℤ × ℤ × ℤ) × ℕ → Set Point2 := fun p =>
    twistedProjection f '' (gridCubeCompactCover δ p.1 p.2)
  have h_image_eq : twistedProjection f '' Y.union =
      ⋃ p ∈ (activeCells ×ˢ Set.univ), C p := by
    rw [h_union_eq, Set.image_iUnion₂]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨cell, hcell, hx⟩
      have h3 : twistedProjection f '' (wz1PaperGridCube δ cell) =
          ⋃ n : ℕ, twistedProjection f '' (gridCubeCompactCover δ cell n) := by
        rw [gridCubeCompactCover_cover hδ cell, Set.image_iUnion]
      rw [h3] at hx
      have h4 : ∃ (n : ℕ), x ∈ twistedProjection f '' (gridCubeCompactCover δ cell n) :=
        Set.mem_iUnion.mp hx
      rcases h4 with ⟨n, hn⟩
      have h6 : (cell, n) ∈ (activeCells ×ˢ Set.univ) := by
        exact Set.mem_prod.mpr ⟨hcell, Set.mem_univ n⟩
      exact ⟨(cell, n), h6, hn⟩
    · rintro ⟨p, hp, hxp⟩
      have hcell : p.1 ∈ activeCells := (Set.mem_prod.mp hp).1
      have h7 : C p ⊆ twistedProjection f '' (wz1PaperGridCube δ p.1) := by
        have h8 : gridCubeCompactCover δ p.1 p.2 ⊆ wz1PaperGridCube δ p.1 := by
          rw [gridCubeCompactCover_cover hδ p.1]
          <;> exact Set.subset_iUnion_of_subset p.2 (Set.Subset.refl _)
        exact Set.image_mono h8
      exact ⟨p.1, hcell, h7 hxp⟩
  rw [h_image_eq]
  apply MeasurableSet.biUnion (h_fin.prod Set.countable_univ)
  rintro ⟨cell, n⟩ _
  have h_compact : IsCompact (gridCubeCompactCover δ cell n) :=
    gridCubeCompactCover_compact hδ cell n
  have h_image_compact : IsCompact (C (cell, n)) :=
    h_compact.image (continuous_twistedProjection f)
  exact h_image_compact.measurableSet

/-- Specialized AD volume bound on [-3,3]. -/
lemma paper_ad_volume_on_interval_3
    {E : Set ℝ} {δ α : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 E δ α C)
    (hδ : 0 < δ) (hδ_le : δ ≤ 6)
    (hE : E ⊆ Set.Icc (-3) 3) :
    volume E ≤ 2 * C * Kakeya.realRpowENN 6 α * Kakeya.realRpowENN δ (1 - α) := by
  have hδ_le2 : δ ≤ 2 * (3 : ℝ) := by linarith
  have h := paper_ad_volume_on_interval (L := (3 : ℝ)) hAD hδ (by norm_num) hδ_le2 hE
  have h6 : (2 * (3 : ℝ)) = (6 : ℝ) := by norm_num
  rw [h6] at h
  exact h

-- ============================================================================
-- Runtime-slope volume bound under a pre-frozen scalar budget
-- ============================================================================

/-- Exact-slice paper AD controls the twisted-projection area for an arbitrary
ambient slope offset.  The offset enters only through `slopeBound`; callers
must discharge the displayed scalar budget before the runtime configuration
is chosen. -/
theorem pure_wz2_small_twisted_projection_of_global_ad_scalar_budget
    {sigma delta outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (slope : SlopeFunction) {C : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤)
    (hcubical : WZ1PaperIsCubicalShading Y)
    {slopeBound : ℝ} (hslopeBound : 0 ≤ slopeBound)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |slope z| ≤ slopeBound)
    (hglobal : ∀ z : ℝ, ∀ hz : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C)
    (hbudget : 8 *
        (C * Kakeya.realRpowENN
          ((2 * (1 + slopeBound)) / delta) (1 - sigma) *
          ENNReal.ofReal (2 * delta)) ≤
        Kakeya.realRpowENN delta (sigma - outputLoss)) :
    volume (twistedProjection slope '' Y.union) ≤
      Kakeya.realRpowENN delta (sigma - outputLoss) := by
  let U := twistedProjection slope '' Y.union
  let rawBound : ENNReal :=
    C * Kakeya.realRpowENN
      ((2 * (1 + slopeBound)) / delta) (1 - sigma) *
      ENNReal.ofReal (2 * delta)
  have hslice : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      volume (sliceAt U z) ≤ rawBound := by
    intro z hz
    rw [twistedProjection_slice_identity]
    apply PureWZ2PaperADSet1.volume_le_of_subset_Icc (hglobal z hz)
    · linarith
    · nlinarith
    · rintro value ⟨point, ⟨hpoint, _⟩, rfl⟩
      have hbox := paper_shading_in_axisBox hpoint
      have hx : |point 0| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.1
      have hy : |point 1| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      change inner ℝ point (globalGrainDirection (slope z)) ∈ _
      rw [global_grain_inner]
      apply abs_le.mp
      calc
        |point 0 + slope z * point 1| ≤
            |point 0| + |slope z| * |point 1| := by
              simpa [abs_mul] using abs_add_le (point 0) (slope z * point 1)
        _ ≤ 1 + slopeBound * 1 := by
              gcongr
              exact hslope z hz
        _ = 1 + slopeBound := by ring
  have hvertical : ∀ point ∈ U,
      (point 1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    rintro point ⟨source, hsource, rfl⟩
    have hbox := paper_shading_in_axisBox hsource
    have hz : |source 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    simpa [twistedProjection] using (abs_le.mp hz)
  have hmeasurable : MeasurableSet U :=
    cubicalUnion_image_measurable hcubical hdelta
  calc
    volume U ≤ ENNReal.ofReal 2 * rawBound :=
      volume_by_slices hmeasurable hvertical hslice
    _ ≤ 8 * rawBound := by
      simpa using
        (mul_le_mul_right' (by norm_num : (2 : ENNReal) ≤ 8) rawBound)
    _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := hbudget

end Kakeya.Assouad

end
