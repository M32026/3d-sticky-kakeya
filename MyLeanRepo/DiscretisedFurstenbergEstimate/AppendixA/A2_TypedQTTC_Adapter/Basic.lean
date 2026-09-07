module

/-
  A2 Typed QTTC Adapter v3: bridge typed dyadic QTTC to A2 AffineLine interface.

  CORRECTIONS from v1/v2:
  1. Exact dyadic levels n, m as parameters (no approximate selection)
  2. T'_affine = ORIGINAL preimages: (T p).filter (fun ℓ => snapTube n ℓ ∈ T'_dyadic p)
  3. Coarse C'_affine = parent reps dyadicTubeToA2 U (NOT subset of fine family)
  4. Added hC'_slope, hC'_v, hC'_b, hC'_near output fields
  5. PointFiber upper bound via ORIGINAL BallGrowth on AffineLine (geometric constant noted)
  6. PointFiber lower bound via sourceParent ↔ InParent bijection

  Pipeline:
  1. Snap AffineLine tubes to DyadicTube n
  2. Transfer BallGrowth → run typed QTTC
  3. Thin coarse set (44×44 coloring) → AffineLine Δ-separation
  4. Retain original AffineLines whose snap was selected
  5. PointFiber: InParent on original ↔ sourceParent on snapped
  6. Absorb 1936x thinning into K; S-set transfer 1936 × 88^s

  Whiteprint node: appendix_a_alternative / a2_typed_qttc_adapter
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Thinning
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept InParent parentCell pointFiber)
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
  (snapTube dyadicTubeToA2 dyadicTubeToA2_slope dyadicTubeToA2_intercept
   sourceParent_snap_iff_inParent ballGrowth_transfer_snap snap_fiber_bound)
open DirecretisedFurstenbergEstimate.AppendixA.A2Thinning (thin_coarse_tubes_affine_separated)
open DirecretisedFurstenbergEstimate.AppendixA.A2Helpers
  (perpendicular_to_algebraic_distance c2_bound_helper
   dyadicDelta_div_refinement floor_real_ediv
   coarse_slope_index_floor coarse_intercept_index_floor)
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
  (qttc_for_dyadicTubes globalCoarseG pointFiberG sp)
open LemmaE (affineLineParams)
open DiscretisedFurstenbergEstimate.InductionOnScales (tubeParamDistLinf dist_le_two_linf)
open DirecretisedFurstenbergEstimate.InductionOnScales (coarseTubeToM refinementFactor)
open DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure (sourceParent)
open DyadicToAffineAdapters (toAffineLine_co_lipschitz)
open DyadicCardToNcover (tubeDirV lineOfSlopeIntercept_direction toAffineLine)
open CoordinatePartition (swapCoords swapCoordsLI)

abbrev Plane := EuclideanPlane


/-- If ⌊x⌋ = ⌊y⌋ then |x - y| < 1. -/
lemma floor_eq_abs_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  let k : ℤ := ⌊x⌋
  have hk : ⌊y⌋ = k := h.symm
  have h1 : (k : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (k : ℝ) ≤ y := by rw [←hk]; exact Int.floor_le y
  have h4 : y < (k : ℝ) + 1 := by rw [←hk]; exact Int.lt_floor_add_one y
  have h5 : x - y < 1 := by linarith
  have h6 : y - x < 1 := by linarith
  rw [abs_lt] <;> constructor <;> linarith

/-- For dyadic r = 2^{-k}, if |x| ≤ 1 then |floor(x/r) * r| ≤ 1.
    Because 1/r = 2^k is an integer, so -1 and 1 are grid points. -/
lemma floor_dyadic_bound_one (x : ℝ) (hx : |x| ≤ 1) {k : ℕ} :
    |(⌊x / dyadicDelta k⌋ : ℝ) * dyadicDelta k| ≤ 1 := by
  let r := dyadicDelta k
  have hr_pos : 0 < r := dyadicDelta_pos k
  let N : ℕ := 2 ^ k
  have h_int : (1 : ℝ) / r = (N : ℝ) := by
    simp [r, dyadicDelta, N] <;> field_simp <;> ring_nf <;> norm_cast
  have h_le : x ≤ 1 := by linarith [abs_le.mp hx]
  have h_ge : -1 ≤ x := by linarith [abs_le.mp hx]
  have h_floor_le : (⌊x / r⌋ : ℝ) ≤ (1 : ℝ) / r := by
    have h1 : x / r ≤ (1 : ℝ) / r := by gcongr
    have h2 : (⌊x / r⌋ : ℝ) ≤ x / r := Int.floor_le (x / r)
    linarith
  have h_floor_ge : -(1 : ℝ) / r ≤ (⌊x / r⌋ : ℝ) := by
    have h1 : -(1 : ℝ) / r ≤ x / r := by gcongr
    have h2 : x / r < (⌊x / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / r)
    have h3 : (⌊-(1 : ℝ) / r⌋ : ℝ) = -(1 : ℝ) / r := by
      have h4 : (1 : ℝ) / r = (N : ℝ) := h_int
      have h5 : -(1 : ℝ) / r = -((1 : ℝ) / r) := by ring
      rw [h5, h4]
      have h6 : (⌊-(N : ℝ)⌋ : ℝ) = -(N : ℝ) := by
        have h7 : ⌊-(N : ℝ)⌋ = - (N : ℤ) := by
          apply Int.floor_eq_iff.mpr
          constructor <;> norm_cast <;> omega
        exact_mod_cast h7
      exact h6
    have h4 : (⌊-(1 : ℝ) / r⌋ : ℝ) ≤ (⌊x / r⌋ : ℝ) := by gcongr <;> linarith
    rw [h3] at h4 <;> exact h4
  have h5 : -(1 : ℝ) ≤ (⌊x / r⌋ : ℝ) * r := by
    calc -(1 : ℝ)
      = (-(1 : ℝ) / r) * r := by field_simp [hr_pos.ne'] <;> ring
    _ ≤ (⌊x / r⌋ : ℝ) * r := by gcongr
  have h6 : (⌊x / r⌋ : ℝ) * r ≤ (1 : ℝ) := by
    calc (⌊x / r⌋ : ℝ) * r
      ≤ ((1 : ℝ) / r) * r := by gcongr
    _ = (1 : ℝ) := by field_simp [hr_pos.ne'] <;> ring
  rw [abs_le] <;> constructor <;> linarith

/-- For dyadic r = 2^{-k}, if |x| ≤ 2 then |floor(x/r) * r| ≤ 2.
    Because 2/r = 2^{k+1} is a natural number, so floor bounds are integers. -/
lemma floor_dyadic_bound_two (x : ℝ) (hx : |x| ≤ 2) {k : ℕ} :
    |(⌊x / dyadicDelta k⌋ : ℝ) * dyadicDelta k| ≤ 2 := by
  let r := dyadicDelta k
  have hr_pos : 0 < r := dyadicDelta_pos k
  let N : ℕ := 2 ^ (k + 1)
  have h_int : (2 : ℝ) / r = (N : ℝ) := by
    simp [r, dyadicDelta, N] <;> field_simp <;> ring_nf <;> norm_cast
  have h_le : x ≤ 2 := by linarith [abs_le.mp hx]
  have h_ge : -2 ≤ x := by linarith [abs_le.mp hx]
  have h_div_le : x / r ≤ (N : ℝ) := by
    have h1 : x / r ≤ (2 : ℝ) / r := by gcongr
    rw [h_int] at h1; exact h1
  have h_div_ge : -(N : ℝ) ≤ x / r := by
    have h1 : -(2 : ℝ) / r ≤ x / r := by gcongr
    have h2 : -(2 : ℝ) / r = -(N : ℝ) := by
      have h3 : -(2 : ℝ) / r = -((2 : ℝ) / r) := by ring
      rw [h3, h_int] <;> ring
    rw [h2] at h1; exact h1
  have h_floor_le : (⌊x / r⌋ : ℝ) ≤ (N : ℝ) := by
    have h1 : (⌊x / r⌋ : ℝ) ≤ x / r := Int.floor_le (x / r)
    linarith
  have h_floor_ge : -(N : ℝ) ≤ (⌊x / r⌋ : ℝ) := by
    have h1 : x / r < (⌊x / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / r)
    have h2 : (⌊-(N : ℝ)⌋ : ℤ) = -(N : ℤ) := by
      have h3 : ⌊-(N : ℝ)⌋ = -⌈(N : ℝ)⌉ := by
        exact Int.floor_neg
      rw [h3]
      have h4 : ⌈(N : ℝ)⌉ = (N : ℤ) := by
        simp [Int.ceil_natCast]
      rw [h4] <;> rfl
    have h3 : (⌊-(N : ℝ)⌋ : ℝ) ≤ (⌊x / r⌋ : ℝ) := by
      gcongr <;> linarith
    rw [h2] at h3 <;> exact_mod_cast h3
  have h5 : -(2 : ℝ) ≤ (⌊x / r⌋ : ℝ) * r := by
    calc -(2 : ℝ)
      = (-(N : ℝ)) * r := by rw [show (-(N : ℝ)) * r = -((N : ℝ) * r) by ring, ←h_int] <;> field_simp [hr_pos.ne'] <;> ring
    _ ≤ (⌊x / r⌋ : ℝ) * r := by gcongr
  have h6 : (⌊x / r⌋ : ℝ) * r ≤ (2 : ℝ) := by
    calc (⌊x / r⌋ : ℝ) * r
      ≤ ((N : ℝ)) * r := by gcongr
    _ = (2 : ℝ) := by rw [←h_int] <;> field_simp [hr_pos.ne'] <;> ring
  have h7 : |(⌊x / r⌋ : ℝ) * r| ≤ 2 := by
    rw [abs_le] <;> constructor <;> linarith
  exact h7

/-- For dyadic r = 2^{-k}, if |x| ≤ 3 then |floor(x/r) * r| ≤ 3.
    Because 3/r = 3 * 2^k is a natural number, so floor bounds are integers. -/
lemma floor_dyadic_bound_three (x : ℝ) (hx : |x| ≤ 3) {k : ℕ} :
    |(⌊x / dyadicDelta k⌋ : ℝ) * dyadicDelta k| ≤ 3 := by
  let r := dyadicDelta k
  have hr_pos : 0 < r := dyadicDelta_pos k
  let N : ℕ := 3 * 2 ^ k
  have h_int : (3 : ℝ) / r = (N : ℝ) := by
    simp [r, dyadicDelta, N] <;> field_simp <;> ring_nf <;> norm_cast
  have h_le : x ≤ 3 := by linarith [abs_le.mp hx]
  have h_ge : -3 ≤ x := by linarith [abs_le.mp hx]
  have h_div_le : x / r ≤ (N : ℝ) := by
    have h1 : x / r ≤ (3 : ℝ) / r := by gcongr
    rw [h_int] at h1; exact h1
  have h_div_ge : -(N : ℝ) ≤ x / r := by
    have h1 : -(3 : ℝ) / r ≤ x / r := by gcongr
    have h2 : -(3 : ℝ) / r = -(N : ℝ) := by
      have h3 : -(3 : ℝ) / r = -((3 : ℝ) / r) := by ring
      rw [h3, h_int] <;> ring
    rw [h2] at h1; exact h1
  have h_floor_le : (⌊x / r⌋ : ℝ) ≤ (N : ℝ) := by
    have h1 : (⌊x / r⌋ : ℝ) ≤ x / r := Int.floor_le (x / r)
    linarith
  have h_floor_ge : -(N : ℝ) ≤ (⌊x / r⌋ : ℝ) := by
    have h1 : x / r < (⌊x / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / r)
    have h2 : (⌊-(N : ℝ)⌋ : ℤ) = -(N : ℤ) := by
      have h3 : ⌊-(N : ℝ)⌋ = -⌈(N : ℝ)⌉ := by exact Int.floor_neg
      rw [h3]
      have h4 : ⌈(N : ℝ)⌉ = (N : ℤ) := by simp [Int.ceil_natCast]
      rw [h4] <;> rfl
    have h3 : (⌊-(N : ℝ)⌋ : ℝ) ≤ (⌊x / r⌋ : ℝ) := by
      gcongr <;> linarith
    rw [h2] at h3 <;> exact_mod_cast h3
  have h5 : -(3 : ℝ) ≤ (⌊x / r⌋ : ℝ) * r := by
    calc -(3 : ℝ)
      = (-(N : ℝ)) * r := by rw [show (-(N : ℝ)) * r = -((N : ℝ) * r) by ring, ←h_int] <;> field_simp [hr_pos.ne'] <;> ring
    _ ≤ (⌊x / r⌋ : ℝ) * r := by gcongr
  have h6 : (⌊x / r⌋ : ℝ) * r ≤ (3 : ℝ) := by
    calc (⌊x / r⌋ : ℝ) * r
      ≤ ((N : ℝ)) * r := by gcongr
    _ = (3 : ℝ) := by rw [←h_int] <;> field_simp [hr_pos.ne'] <;> ring
  have h7 : |(⌊x / r⌋ : ℝ) * r| ≤ 3 := by
    rw [abs_le] <;> constructor <;> linarith
  exact h7

/-- Injectivity of dyadicTubeToA2. -/
lemma dyadicTubeToA2_injective {m : ℕ} :
    Function.Injective (dyadicTubeToA2 : DyadicTube m → AffineLine) := by
  intro U1 U2 h
  have hs : U1.slope = U2.slope := by
    have h1 := congr_arg tubeSlope h
    simpa [dyadicTubeToA2_slope] using h1
  have hi : U1.intercept = U2.intercept := by
    have h1 := congr_arg tubeIntercept h
    simpa [dyadicTubeToA2_intercept] using h1
  have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have ha : (U1.a : ℝ) = (U2.a : ℝ) := by
    have h_eq : (U1.a : ℝ) * dyadicDelta m = (U2.a : ℝ) * dyadicDelta m := hs
    apply mul_left_cancel₀ hδ_pos.ne'
    linarith
  have hb : (U1.b : ℝ) = (U2.b : ℝ) := by
    have h_eq : (U1.b : ℝ) * dyadicDelta m = (U2.b : ℝ) * dyadicDelta m := hi
    apply mul_left_cancel₀ hδ_pos.ne'
    linarith
  have ha' : U1.a = U2.a := by exact_mod_cast ha
  have hb' : U1.b = U2.b := by exact_mod_cast hb
  cases U1 <;> cases U2 <;> simp_all

/-- L1 DyadicTube dist ≤ 44 × AffineLine dist of images. -/
lemma dyadicTube_dist_le_44_affine {m : ℕ} (U1 U2 : DyadicTube m)
    (h_s1 : |U1.slope| ≤ 1) (h_s2 : |U2.slope| ≤ 1)
    (h_i1 : |U1.intercept| ≤ 3) (h_i2 : |U2.intercept| ≤ 3) :
    U1.dist U2 ≤ 44 * dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2) := by
  have h1 : U1.dist U2 ≤ 2 * tubeParamDistLinf U1 U2 :=
    dist_le_two_linf U1 U2
  have h2 : tubeParamDistLinf U1 U2 ≤
      22 * dist (toAffineLine U1) (toAffineLine U2) :=
    toAffineLine_co_lipschitz U1 U2 h_s1 h_s2 h_i2
  have h3 : dist (toAffineLine U1) (toAffineLine U2) =
      dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2) := by
    simp [dyadicTubeToA2, CoordinatePartition.swapLine_isometry.dist_eq]
  rw [h3] at h2; linarith

/-- getDirV of dyadicTubeToA2 U has nonzero y-component.
    Direction is span{swapCoords(tubeDirV U.slope)} = span{(U.slope, 1)},
    so any nonzero direction vector has second component ≠ 0. -/
lemma dyadicTubeToA2_getDirV_ne_zero {m : ℕ} (U : DyadicTube m) :
    (LemmaE.getDirV (dyadicTubeToA2 U)) 1 ≠ 0 := by
  let c := dyadicTubeToA2 U
  let v := LemmaE.getDirV c
  have hv_dir : v ∈ c.1.direction := (LemmaE.getDirV_spec c).1
  have hv_ne : v ≠ 0 := (LemmaE.getDirV_spec c).2
  have h_dir : c.1.direction = Submodule.span ℝ {swapCoords (tubeDirV U.slope)} := by
    have h1 : (toAffineLine U).1.direction = Submodule.span ℝ {tubeDirV U.slope} :=
      lineOfSlopeIntercept_direction U.slope U.intercept
    have h2 : c.1.direction =
        Submodule.map (swapCoordsLI : EuclideanPlane →ₗ[ℝ] EuclideanPlane)
          (toAffineLine U).1.direction := by
      exact AffineSubspace.map_direction _ _
    rw [h2, h1]
    simp [Submodule.map_span]
    <;> rfl
  rw [h_dir] at hv_dir
  have h3 : ∃ (k : ℝ), v = k • swapCoords (tubeDirV U.slope) := by
    rw [Submodule.mem_span_singleton] at hv_dir
    rcases hv_dir with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  rcases h3 with ⟨k, hk⟩
  have hk_ne : k ≠ 0 := by
    by_contra h
    rw [h, zero_smul] at hk
    exact hv_ne hk
  have h4 : (swapCoords (tubeDirV U.slope)) 1 = 1 := by
    simp [swapCoords, tubeDirV, TubesAndSlopes.mkPlane_apply0]
    <;> rfl
  have h5 : v 1 = k := by
    rw [hk]
    simp [h4] <;> ring
  rw [h5]
  exact hk_ne

/-- Geometric constant for pointFiber upper bound.
    Parent cell diameter in AffineLine metric ≤ 6*Δ via generic antilipschitz (B=3).
    Absorb this constant in A2_Main / A2_Smallness. -/
def GEOM_CONST (s : ℝ) : ℝ := (6 : ℝ)^s

/-- Ceiling division bound: `n ≤ d * ceil(n/d)` where `ceil(n/d) = (n+d-1)/d`. -/
lemma ceil_div_mul_bound {n d : ℕ} (hd : 0 < d) : n ≤ d * ((n + d - 1) / d) := by
  set q : ℕ := (n + d - 1) / d with hq
  by_contra h
  have h' : d * q + 1 ≤ n := by omega
  have h9 : d * q + d ≤ n + d - 1 := by
    have h10 : d ≥ 1 := by omega
    omega
  have h'' : (q + 1) * d ≤ n + d - 1 := by
    have h11 : (q + 1) * d = d * q + d := by ring
    rw [h11]
    exact h9
  have h3 : q + 1 ≤ (n + d - 1) / d := by
    exact (Nat.le_div_iff_mul_le hd).mpr h''
  rw [hq] at h3
  omega

/-- If `n < d * k`, then `ceil(n/d) ≤ k`. -/
lemma ceil_div_le {n d k : ℕ} (hd : 0 < d) (h : n < d * k) : (n + d - 1) / d ≤ k := by
  by_contra h2
  have h3 : k + 1 ≤ (n + d - 1) / d := by omega
  have h4 : (k + 1) * d ≤ n + d - 1 := (Nat.le_div_iff_mul_le hd).mp h3
  have h5 : d * (k + 1) ≤ n + d - 1 := by
    have h6 : d * (k + 1) = (k + 1) * d := by ring
    rw [h6]
    exact h4
  have h7 : n + d ≤ d * (k + 1) := by
    have h8 : n < d * k := h
    have h9 : n + d ≤ d * k + d := by omega
    have h10 : d * k + d = d * (k + 1) := by ring
    rw [h10] at h9
    exact h9
  omega

/-- Ceiling division: `ceil(n/d) ≤ n` when `n > 0` and `d > 0`. -/
lemma ceil_div_le_self {n d : ℕ} (hn : 0 < n) (hd : 0 < d) : (n + d - 1) / d ≤ n := by
  apply Nat.div_le_of_le_mul
  have h1 : n ≥ 1 := by omega
  have h2 : d ≥ 1 := by omega
  have h3 : d * n ≥ n + d - 1 := by
    have h4 : d * n = n + (d - 1) * n := by
      cases d with
      | zero => omega
      | succ d' =>
        simp [Nat.mul_succ, Nat.add_assoc] <;> ring
    rw [h4]
    have h5 : (d - 1) * n ≥ d - 1 := by
      have h6 : d - 1 ≥ 0 := by omega
      have h7 : n ≥ 1 := by omega
      by_cases h8 : d = 1
      · simp [h8]
      · have h9 : d ≥ 2 := by omega
        have h10 : (d - 1) * n ≥ (d - 1) * 1 := Nat.mul_le_mul_left (d - 1) h7
        simpa using h10
    omega
  exact h3

/-- Helper: bound on K in terms of A and log(2/Δ). -/
lemma k_bound_helper (A_typed K_typed D Δ s : ℝ)
    (hA_one : 1 ≤ A_typed) (hK_one : 1 ≤ K_typed) (hD_one : 1 ≤ D)
    (hs : 0 ≤ s) (hΔ_pos : 0 < Δ) (hΔ_le_half : Δ ≤ 1 / 2)
    (hK_bound : K_typed ≤ A_typed * Real.rpow (Real.log (2 / Δ)) A_typed)
    (A K : ℝ) (hA_def : A = A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s)
    (hK_def : K = K_typed * D * 1936) :
    K ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
  have hA_ge : A_typed ≤ A := by
    rw [hA_def]
    have h3 : 1 ≤ (88 : ℝ)^s := by
      have h : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) hs
      have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
      rw [h9] at h; exact h
    have h4 : 1 ≤ (40 : ℝ)^s := by
      have h : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) hs
      have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
      rw [h9] at h; exact h
    have h7 : 0 ≤ D := le_trans zero_le_one hD_one
    have h81 : 1 ≤ D * (1936 : ℝ) := by
      have h11 : (1 : ℝ) ≤ (1936 : ℝ) := by norm_num
      have h12 : D * 1 ≤ D * (1936 : ℝ) := mul_le_mul_of_nonneg_left h11 h7
      have h13 : D * 1 = D := by ring
      rw [h13] at h12
      exact le_trans hD_one h12
    have h81' : 0 ≤ D * (1936 : ℝ) := by positivity
    have h82 : 1 ≤ D * (1936 : ℝ) * (88 : ℝ)^s := by
      have h : (1 : ℝ) * (1 : ℝ) ≤ (D * (1936 : ℝ)) * (88 : ℝ)^s := by
        apply mul_le_mul h81 h3 (by positivity) h81'
      simpa using h
    have hpos2 : 0 ≤ D * (1936 : ℝ) * (88 : ℝ)^s := by positivity
    have h8 : 1 ≤ D * (1936 : ℝ) * (88 : ℝ)^s * (40 : ℝ)^s := by
      have h : (1 : ℝ) * (1 : ℝ) ≤ (D * (1936 : ℝ) * (88 : ℝ)^s) * (40 : ℝ)^s := by
        apply mul_le_mul h82 h4 (by positivity) hpos2
      simpa using h
    have hA_nonneg : 0 ≤ A_typed := le_trans zero_le_one hA_one
    have h10 : A_typed ≤ A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by
      have h : A_typed * 1 ≤ A_typed * (D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s) := by
        exact mul_le_mul_of_nonneg_left h8 hA_nonneg
      simpa [mul_assoc] using h
    exact h10
  have hLog_gt_one : 1 < Real.log (2 / Δ) := by
    have h1 : 2 / Δ ≥ 4 := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : Δ ≤ 1 / 2 := hΔ_le_half
      calc 2 / Δ ≥ 2 / (1 / 2) := by gcongr
      _ = 4 := by norm_num
    have h4 : (4 : ℝ) ≤ 2 / Δ := h1
    have h5 : Real.log 4 ≤ Real.log (2 / Δ) := Real.log_le_log (by norm_num) h4
    have h6 : (1 : ℝ) < Real.log 4 := by
      have h7 : Real.exp 1 < (4 : ℝ) := by
        have h8 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
        linarith
      have h9 : (1 : ℝ) < Real.log 4 := by
        have h10 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h7
        have h11 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
        rw [h11] at h10
        exact h10
      exact h9
    linarith
  have h_base : 1 ≤ Real.log (2 / Δ) := by linarith [hLog_gt_one]
  have hRpow_mono : Real.rpow (Real.log (2 / Δ)) A_typed ≤ Real.rpow (Real.log (2 / Δ)) A :=
    Real.rpow_le_rpow_of_exponent_le h_base hA_ge
  have h3 : 1 ≤ (88 : ℝ)^s := by
    have h : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) hs
    have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
    rw [h9] at h; exact h
  have h4 : 1 ≤ (40 : ℝ)^s := by
    have h : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) hs
    have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
    rw [h9] at h; exact h
  have h15 : Real.rpow (Real.log (2 / Δ)) A_typed ≤
      (88 : ℝ)^s * (40 : ℝ)^s * Real.rpow (Real.log (2 / Δ)) A := by
    have h16 : 0 ≤ Real.rpow (Real.log (2 / Δ)) A :=
      Real.rpow_nonneg (by linarith [h_base]) A
    have h17 : 1 ≤ (88 : ℝ)^s * (40 : ℝ)^s := by
      calc 1 = 1 * 1 := by ring
      _ ≤ (88 : ℝ)^s * (40 : ℝ)^s := by
        apply mul_le_mul h3 h4 (by positivity) (by positivity)
    have h18 : 1 * Real.rpow (Real.log (2 / Δ)) A ≤
        (88 : ℝ)^s * (40 : ℝ)^s * Real.rpow (Real.log (2 / Δ)) A := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right h17 h16
    calc Real.rpow (Real.log (2 / Δ)) A_typed
      ≤ Real.rpow (Real.log (2 / Δ)) A := hRpow_mono
    _ = 1 * Real.rpow (Real.log (2 / Δ)) A := by ring
    _ ≤ (88 : ℝ)^s * (40 : ℝ)^s * Real.rpow (Real.log (2 / Δ)) A := h18
  have hpos_D : 0 ≤ D := le_trans zero_le_one hD_one
  have h_step1 : K_typed * D ≤ (A_typed * Real.rpow (Real.log (2 / Δ)) A_typed) * D :=
    mul_le_mul_of_nonneg_right hK_bound hpos_D
  have h_step2 : (K_typed * D) * 1936 ≤ ((A_typed * Real.rpow (Real.log (2 / Δ)) A_typed) * D) * 1936 :=
    mul_le_mul_of_nonneg_right h_step1 (by norm_num)
  have hpos_AD : 0 ≤ A_typed * D * 1936 := by positivity
  have h_main : K_typed * D * 1936 ≤ A * Real.rpow (Real.log (2 / Δ)) A := by
    calc K_typed * D * 1936
      ≤ (A_typed * Real.rpow (Real.log (2 / Δ)) A_typed) * D * 1936 := h_step2
    _ = A_typed * D * 1936 * Real.rpow (Real.log (2 / Δ)) A_typed := by ring
    _ ≤ A_typed * D * 1936 * ((88 : ℝ)^s * (40 : ℝ)^s * Real.rpow (Real.log (2 / Δ)) A) :=
        mul_le_mul_of_nonneg_left h15 hpos_AD
    _ = (A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s) * Real.rpow (Real.log (2 / Δ)) A := by ring
    _ = A * Real.rpow (Real.log (2 / Δ)) A := by rw [hA_def] <;> ring
  rw [hK_def]
  exact h_main


end DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter
