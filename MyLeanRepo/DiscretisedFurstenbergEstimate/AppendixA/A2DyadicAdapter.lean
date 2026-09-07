module

/-
  A2 Dyadic Adapter: AffineLine ↔ DyadicTube

  Bridges A1's AffineLine tube data (x=ay+b convention) to kestrel's typed
  dyadic QTTC (DyadicTube uses y=mx+b convention internally, but we snap
  using A2's tubeSlope/tubeIntercept directly).

  Key equivalence:
    sourceParent(snapTube(n, ℓ)) = U
      ↔
    InParent(Δ, ℓ, dyadicTubeToA2(U))

  where dyadicTubeToA2(U) := swapLine(toAffineLine U) gives correct
  tubeSlope/tubeIntercept matching U.slope/U.intercept.

  Whiteprint node: appendix_a_alternative / a2_dyadic_adapter
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.InductionOnScales (refinementFactor dyadicDelta_mul_refinement)
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept InParent parentCell)
open DyadicCardToNcover (toAffineLine)
open CoordinatePartition (swapLine swapLine_params_eq)
open TypedDyadicInfrastructure (sourceParent refinementFactor_pos')
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly (globalCoarseG pointFiberG)
open DirecretisedFurstenbergEstimate.InductionOnScales (coarseTubeToM)
open LemmaE (affineLineParams)

abbrev Plane := EuclideanPlane
abbrev FineTube := AffineLine
abbrev CoarseTube := AffineLine

/-! ========================================================================
   1. Output conversion: DyadicTube m → AffineLine (A2 convention)
   ======================================================================== -/

/-- Convert a dyadic coarse tube to an AffineLine in A2's x=ay+b convention.
    Uses swapLine to convert from dyadic y=mx+b convention. -/
def dyadicTubeToA2 {m : ℕ} (U : DyadicTube m) : AffineLine :=
  swapLine (toAffineLine U)

lemma dyadicTubeToA2_slope {m : ℕ} (U : DyadicTube m) :
    tubeSlope (dyadicTubeToA2 U) = U.slope := by
  have h : affineLineParams (dyadicTubeToA2 U) = (U.slope, U.intercept) :=
    swapLine_params_eq U.slope U.intercept
  simpa [tubeSlope] using congr_arg Prod.fst h

lemma dyadicTubeToA2_intercept {m : ℕ} (U : DyadicTube m) :
    tubeIntercept (dyadicTubeToA2 U) = U.intercept := by
  have h : affineLineParams (dyadicTubeToA2 U) = (U.slope, U.intercept) :=
    swapLine_params_eq U.slope U.intercept
  simpa [tubeIntercept] using congr_arg Prod.snd h

/-! ========================================================================
   2. Input snapping: AffineLine → DyadicTube n
   ======================================================================== -/

/-- Snap an AffineLine's (slope, intercept) to the dyadic δ-grid.
    Uses A2's tubeSlope/tubeIntercept (x=ay+b convention) directly. -/
def snapTube (n : ℕ) (ℓ : AffineLine) : DyadicTube n :=
  let δ := dyadicDelta n
  ⟨⌊tubeSlope ℓ / δ⌋, ⌊tubeIntercept ℓ / δ⌋⟩

lemma snapTube_param_dist_le_delta (n : ℕ) (ℓ : AffineLine) :
    |tubeSlope ℓ - (snapTube n ℓ).slope| < dyadicDelta n ∧
    |tubeIntercept ℓ - (snapTube n ℓ).intercept| < dyadicDelta n := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h3 : |tubeSlope ℓ - (snapTube n ℓ).slope| < δ := by
    simp only [DyadicTube.slope, snapTube]
    have h4 : tubeSlope ℓ - (⌊tubeSlope ℓ / δ⌋ : ℝ) * δ =
        δ * (tubeSlope ℓ / δ - (⌊tubeSlope ℓ / δ⌋ : ℝ)) := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h4, abs_mul, abs_of_pos hδ_pos]
    have h5 : |tubeSlope ℓ / δ - (⌊tubeSlope ℓ / δ⌋ : ℝ)| < 1 := by
      rw [abs_lt] <;> constructor <;> linarith [Int.floor_le (tubeSlope ℓ / δ),
        Int.lt_floor_add_one (tubeSlope ℓ / δ)]
    nlinarith
  have h6 : |tubeIntercept ℓ - (snapTube n ℓ).intercept| < δ := by
    simp only [DyadicTube.intercept, snapTube]
    have h7 : tubeIntercept ℓ - (⌊tubeIntercept ℓ / δ⌋ : ℝ) * δ =
        δ * (tubeIntercept ℓ / δ - (⌊tubeIntercept ℓ / δ⌋ : ℝ)) := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h7, abs_mul, abs_of_pos hδ_pos]
    have h8 : |tubeIntercept ℓ / δ - (⌊tubeIntercept ℓ / δ⌋ : ℝ)| < 1 := by
      rw [abs_lt] <;> constructor <;> linarith [Int.floor_le (tubeIntercept ℓ / δ),
        Int.lt_floor_add_one (tubeIntercept ℓ / δ)]
    nlinarith
  exact ⟨h3, h6⟩

/-! ========================================================================
   3. Key equivalence: sourceParent(snapTube ℓ) = U ↔ InParent Δ ℓ (dyadicTubeToA2 U)
   ======================================================================== -/

/-- Integer division equals floor of real division for positive naturals. -/
private lemma int_ediv_eq_floor_div (a : ℤ) (k : ℕ) (hk_pos : 0 < k) :
    a / (k : ℤ) = ⌊(a : ℝ) / (k : ℝ)⌋ := by
  let c : ℤ := a / (k : ℤ)
  have hk_pos' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk_pos
  have hk_ne_zero : (k : ℤ) ≠ 0 := by linarith
  have h3 : c * (k : ℤ) ≤ a := Int.ediv_mul_le a hk_ne_zero
  have h4 : a < (c + 1) * (k : ℤ) := by
    by_contra h5
    have h6 : (c + 1) * (k : ℤ) ≤ a := by linarith
    have h7 : c + 1 ≤ a / (k : ℤ) := Int.le_ediv_of_mul_le hk_pos' h6
    rw [show a / (k : ℤ) = c from rfl] at h7 <;> omega
  have h_goal : ⌊(a : ℝ) / (k : ℝ)⌋ = c := by
    apply Int.floor_eq_iff.mpr
    constructor
    · have h17 : (c : ℝ) * (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast h3
      calc (c : ℝ)
        = ((c : ℝ) * (k : ℝ)) / (k : ℝ) := by field_simp [hk_pos.ne'] <;> ring
      _ ≤ (a : ℝ) / (k : ℝ) := by gcongr
    · have h18 : (a : ℝ) < ((c : ℝ) + 1) * (k : ℝ) := by exact_mod_cast h4
      calc (a : ℝ) / (k : ℝ)
        < (((c : ℝ) + 1) * (k : ℝ)) / (k : ℝ) := by gcongr
      _ = (c : ℝ) + 1 := by field_simp [hk_pos.ne'] <;> ring
  exact h_goal.symm

/-- Double floor identity: for x : ℝ, δ > 0, k : ℕ, k > 0:
    ⌊(⌊x / δ⌋ : ℝ) / (k : ℝ)⌋ = ⌊x / (δ * (k : ℝ))⌋ -/
private lemma floor_double_floor_real (x : ℝ) (δ : ℝ) (hδ_pos : 0 < δ) (k : ℕ) (hk_pos : 0 < k) :
    ⌊(⌊x / δ⌋ : ℝ) / (k : ℝ)⌋ = ⌊x / (δ * (k : ℝ))⌋ := by
  let a : ℤ := ⌊x / δ⌋
  let c : ℤ := a / (k : ℤ)
  have hk_pos' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk_pos
  have hk_ne_zero : (k : ℤ) ≠ 0 := by linarith
  have h1 : (a : ℝ) ≤ x / δ := Int.floor_le _
  have h2 : x / δ < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : c * (k : ℤ) ≤ a := Int.ediv_mul_le a hk_ne_zero
  have h4 : a < (c + 1) * (k : ℤ) := by
    by_contra h5
    have h6 : (c + 1) * (k : ℤ) ≤ a := by linarith
    have h7 : c + 1 ≤ a / (k : ℤ) := Int.le_ediv_of_mul_le hk_pos' h6
    rw [show a / (k : ℤ) = c from rfl] at h7
    <;> omega
  have h5 : (c : ℝ) * (k : ℝ) ≤ x / δ := by
    have h51 : (c : ℝ) * (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast h3
    exact le_trans h51 h1
  have h6 : x / δ < ((c : ℝ) + 1) * (k : ℝ) := by
    have h61 : (a : ℝ) + 1 ≤ ((c : ℝ) + 1) * (k : ℝ) := by
      have h62 : a + 1 ≤ (c + 1) * (k : ℤ) := by omega
      exact_mod_cast h62
    linarith
  have h7 : (c : ℝ) ≤ x / (δ * (k : ℝ)) := by
    have h8 : (c : ℝ) * (k : ℝ) ≤ x / δ := h5
    have h9 : (c : ℝ) ≤ (x / δ) / (k : ℝ) := by
      calc (c : ℝ)
        = ((c : ℝ) * (k : ℝ)) / (k : ℝ) := by field_simp [hk_pos.ne'] <;> ring
      _ ≤ (x / δ) / (k : ℝ) := by gcongr
    have h10 : (x / δ) / (k : ℝ) = x / (δ * (k : ℝ)) := by
      field_simp [hδ_pos.ne', hk_pos.ne'] <;> ring
    rw [h10] at h9
    exact h9
  have h11 : x / (δ * (k : ℝ)) < (c : ℝ) + 1 := by
    have h12 : x / δ < ((c : ℝ) + 1) * (k : ℝ) := h6
    have h13 : (x / δ) / (k : ℝ) < (c : ℝ) + 1 := by
      calc (x / δ) / (k : ℝ)
        < (((c : ℝ) + 1) * (k : ℝ)) / (k : ℝ) := by gcongr
      _ = (c : ℝ) + 1 := by field_simp [hk_pos.ne'] <;> ring
    have h14 : (x / δ) / (k : ℝ) = x / (δ * (k : ℝ)) := by
      field_simp [hδ_pos.ne', hk_pos.ne'] <;> ring
    rw [h14] at h13
    exact h13
  have h15 : ⌊x / (δ * (k : ℝ))⌋ = c := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast h7, by exact_mod_cast h11⟩
  have h16 : ⌊(a : ℝ) / (k : ℝ)⌋ = c := by
    rw [Int.floor_eq_iff]
    constructor
    · have h17 : (c : ℝ) * (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast h3
      calc (c : ℝ)
        = ((c : ℝ) * (k : ℝ)) / (k : ℝ) := by field_simp [hk_pos.ne'] <;> ring
      _ ≤ (a : ℝ) / (k : ℝ) := by gcongr
    · have h18 : (a : ℝ) < ((c : ℝ) + 1) * (k : ℝ) := by exact_mod_cast h4
      calc (a : ℝ) / (k : ℝ)
        < (((c : ℝ) + 1) * (k : ℝ)) / (k : ℝ) := by gcongr
      _ = (c : ℝ) + 1 := by field_simp [hk_pos.ne'] <;> ring
  rw [h16, h15]

/-- sourceParent of snapped tube equals floor of original params at coarse scale. -/
lemma sourceParent_snap_eq {n m : ℕ} (hnm : m ≤ n) (ℓ : AffineLine) :
    (sourceParent hnm (snapTube n ℓ)).a =
      ⌊tubeSlope ℓ / dyadicDelta m⌋ ∧
    (sourceParent hnm (snapTube n ℓ)).b =
      ⌊tubeIntercept ℓ / dyadicDelta m⌋ := by
  let δ := dyadicDelta n
  let Δ := dyadicDelta m
  let R : ℕ := refinementFactor n m
  have hR_pos : 0 < R := by
    dsimp only [R, refinementFactor]
    positivity
  have h_scale : Δ = δ * (R : ℝ) := by
    have h := dyadicDelta_mul_refinement n m hnm
    simpa [R] using h.symm
  have h_a : (sourceParent hnm (snapTube n ℓ)).a =
      (snapTube n ℓ).a / (R : ℤ) := by rfl
  have h_b : (sourceParent hnm (snapTube n ℓ)).b =
      (snapTube n ℓ).b / (R : ℤ) := by rfl
  constructor
  · rw [h_a, snapTube]
    have h_floor : ((⌊tubeSlope ℓ / δ⌋ : ℤ) / (R : ℤ)) =
        ⌊(⌊tubeSlope ℓ / δ⌋ : ℝ) / (R : ℝ)⌋ :=
      int_ediv_eq_floor_div ⌊tubeSlope ℓ / δ⌋ R hR_pos
    rw [h_floor]
    have h_main := floor_double_floor_real (tubeSlope ℓ) δ (dyadicDelta_pos n) R hR_pos
    rw [h_main]
    have h_final : ⌊tubeSlope ℓ / (δ * (R : ℝ))⌋ = ⌊tubeSlope ℓ / Δ⌋ := by
      rw [show δ * (R : ℝ) = Δ from h_scale.symm]
    exact h_final
  · rw [h_b, snapTube]
    have h_floor : ((⌊tubeIntercept ℓ / δ⌋ : ℤ) / (R : ℤ)) =
        ⌊(⌊tubeIntercept ℓ / δ⌋ : ℝ) / (R : ℝ)⌋ :=
      int_ediv_eq_floor_div ⌊tubeIntercept ℓ / δ⌋ R hR_pos
    rw [h_floor]
    have h_main := floor_double_floor_real (tubeIntercept ℓ) δ (dyadicDelta_pos n) R hR_pos
    rw [h_main]
    have h_final : ⌊tubeIntercept ℓ / (δ * (R : ℝ))⌋ = ⌊tubeIntercept ℓ / Δ⌋ := by
      rw [show δ * (R : ℝ) = Δ from h_scale.symm]
    exact h_final

/-- parentCell of a dyadic tube's A2 representation equals its integer indices. -/
lemma dyadicTube_parentCell {m : ℕ} (U : DyadicTube m) (hΔ_pos : 0 < dyadicDelta m) :
    parentCell (dyadicDelta m) hΔ_pos (dyadicTubeToA2 U) = (U.a, U.b) := by
  have h_s : tubeSlope (dyadicTubeToA2 U) = U.slope := dyadicTubeToA2_slope U
  have h_i : tubeIntercept (dyadicTubeToA2 U) = U.intercept := dyadicTubeToA2_intercept U
  have h1 : ⌊tubeSlope (dyadicTubeToA2 U) / dyadicDelta m⌋ = U.a := by
    rw [h_s]
    have h2 : U.slope = (U.a : ℝ) * dyadicDelta m := by
      simp [DyadicTube.slope] <;> ring
    rw [h2]
    have h3 : ((U.a : ℝ) * dyadicDelta m) / dyadicDelta m = (U.a : ℝ) := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h3]
    simp
  have h4 : ⌊tubeIntercept (dyadicTubeToA2 U) / dyadicDelta m⌋ = U.b := by
    rw [h_i]
    have h5 : U.intercept = (U.b : ℝ) * dyadicDelta m := by
      simp [DyadicTube.intercept] <;> ring
    rw [h5]
    have h6 : ((U.b : ℝ) * dyadicDelta m) / dyadicDelta m = (U.b : ℝ) := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h6]
    simp
  simp [parentCell, h1, h4]

/-- The key incidence equivalence. -/
lemma sourceParent_snap_iff_inParent
    {n m : ℕ} (hnm : m ≤ n) (ℓ : AffineLine) (U : DyadicTube m)
    (hΔ_pos : 0 < dyadicDelta m) :
    sourceParent hnm (snapTube n ℓ) = U ↔
    InParent (dyadicDelta m) hΔ_pos ℓ (dyadicTubeToA2 U) := by
  have h_sp := sourceParent_snap_eq hnm ℓ
  have h_parent_a : (parentCell (dyadicDelta m) hΔ_pos ℓ).1 =
      ⌊tubeSlope ℓ / dyadicDelta m⌋ := by rfl
  have h_parent_b : (parentCell (dyadicDelta m) hΔ_pos ℓ).2 =
      ⌊tubeIntercept ℓ / dyadicDelta m⌋ := by rfl
  have h_parent_U : parentCell (dyadicDelta m) hΔ_pos (dyadicTubeToA2 U) = (U.a, U.b) :=
    dyadicTube_parentCell U hΔ_pos
  constructor
  · intro h
    have ha : (sourceParent hnm (snapTube n ℓ)).a = U.a := by
      exact congr_arg (fun (x : DyadicTube m) => x.a) h
    have hb : (sourceParent hnm (snapTube n ℓ)).b = U.b := by
      exact congr_arg (fun (x : DyadicTube m) => x.b) h
    have h1 : ⌊tubeSlope ℓ / dyadicDelta m⌋ = U.a := by
      rw [←h_sp.1, ha]
    have h2 : ⌊tubeIntercept ℓ / dyadicDelta m⌋ = U.b := by
      rw [←h_sp.2, hb]
    have h3 : parentCell (dyadicDelta m) hΔ_pos ℓ = (U.a, U.b) := by
      ext <;> simp [h_parent_a, h_parent_b, h1, h2] <;> norm_cast <;> omega
    rw [InParent, h3, h_parent_U]
  · intro h
    rw [InParent] at h
    have h4 : parentCell (dyadicDelta m) hΔ_pos ℓ = parentCell (dyadicDelta m) hΔ_pos (dyadicTubeToA2 U) := h
    rw [h_parent_U] at h4
    have h5 : (parentCell (dyadicDelta m) hΔ_pos ℓ).1 = U.a := by
      rw [h4] <;> simp
    have h6 : (parentCell (dyadicDelta m) hΔ_pos ℓ).2 = U.b := by
      rw [h4] <;> simp
    have h7 : ⌊tubeSlope ℓ / dyadicDelta m⌋ = U.a := by
      simpa [h_parent_a] using h5
    have h8 : ⌊tubeIntercept ℓ / dyadicDelta m⌋ = U.b := by
      simpa [h_parent_b] using h6
    have ha : (sourceParent hnm (snapTube n ℓ)).a = U.a := by
      rw [h_sp.1, h7]
    have hb : (sourceParent hnm (snapTube n ℓ)).b = U.b := by
      rw [h_sp.2, h8]
    have h_main : sourceParent hnm (snapTube n ℓ) = U := by
      set T_sp := sourceParent hnm (snapTube n ℓ) with hT_sp
      have ha' : T_sp.a = U.a := ha
      have hb' : T_sp.b = U.b := hb
      have h_eta1 : T_sp = DyadicTube.mk (n := m) T_sp.a T_sp.b := by simp
      have h_eta2 : U = DyadicTube.mk (n := m) U.a U.b := by simp
      rw [h_eta1, h_eta2]
      <;> congr <;> assumption
    exact h_main

/-! ========================================================================
   5. BallGrowth transfer: AffineLine → DyadicTube via snapping
   ======================================================================== -/

/-- If snapTube n ℓ = U, then tubeSlope ℓ lies in [U.a*δ, (U.a+1)*δ). -/
private lemma snap_slope_in_cell {n : ℕ} {δ : ℝ} (hδ_eq : δ = dyadicDelta n)
    {ℓ : AffineLine} {U : DyadicTube n} (h : snapTube n ℓ = U) :
    (U.a : ℝ) * δ ≤ tubeSlope ℓ ∧ tubeSlope ℓ < ((U.a : ℝ) + 1) * δ := by
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> exact dyadicDelta_pos n
  have h1 : ⌊tubeSlope ℓ / δ⌋ = U.a := by
    have h2 : (snapTube n ℓ).a = U.a := by rw [h]
    have h3 : (snapTube n ℓ).a = ⌊tubeSlope ℓ / δ⌋ := by
      simp [snapTube, hδ_eq]
    rw [h3] at h2
    exact h2
  have h3 : (U.a : ℝ) ≤ tubeSlope ℓ / δ := by
    have h4 : (⌊tubeSlope ℓ / δ⌋ : ℝ) ≤ tubeSlope ℓ / δ := Int.floor_le _
    rw [h1] at h4; exact h4
  have h5 : tubeSlope ℓ / δ < (U.a : ℝ) + 1 := by
    have h6 : tubeSlope ℓ / δ < (⌊tubeSlope ℓ / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [h1] at h6; exact h6
  constructor
  · calc (U.a : ℝ) * δ
      = ((U.a : ℝ)) * δ := by ring
    _ ≤ (tubeSlope ℓ / δ) * δ := by gcongr
    _ = tubeSlope ℓ := by field_simp [hδ_pos.ne'] <;> ring
  · calc tubeSlope ℓ
      = (tubeSlope ℓ / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
    _ < (((U.a : ℝ) + 1)) * δ := by gcongr

/-- Same for intercept. -/
private lemma snap_intercept_in_cell {n : ℕ} {δ : ℝ} (hδ_eq : δ = dyadicDelta n)
    {ℓ : AffineLine} {U : DyadicTube n} (h : snapTube n ℓ = U) :
    (U.b : ℝ) * δ ≤ tubeIntercept ℓ ∧ tubeIntercept ℓ < ((U.b : ℝ) + 1) * δ := by
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> exact dyadicDelta_pos n
  have h1 : ⌊tubeIntercept ℓ / δ⌋ = U.b := by
    have h2 : (snapTube n ℓ).b = U.b := by rw [h]
    have h3 : (snapTube n ℓ).b = ⌊tubeIntercept ℓ / δ⌋ := by
      simp [snapTube, hδ_eq]
    rw [h3] at h2
    exact h2
  have h3 : (U.b : ℝ) ≤ tubeIntercept ℓ / δ := by
    have h4 : (⌊tubeIntercept ℓ / δ⌋ : ℝ) ≤ tubeIntercept ℓ / δ := Int.floor_le _
    rw [h1] at h4; exact h4
  have h5 : tubeIntercept ℓ / δ < (U.b : ℝ) + 1 := by
    have h6 : tubeIntercept ℓ / δ < (⌊tubeIntercept ℓ / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [h1] at h6; exact h6
  constructor
  · calc (U.b : ℝ) * δ
      = ((U.b : ℝ)) * δ := by ring
    _ ≤ (tubeIntercept ℓ / δ) * δ := by gcongr
    _ = tubeIntercept ℓ := by field_simp [hδ_pos.ne'] <;> ring
  · calc tubeIntercept ℓ
      = (tubeIntercept ℓ / δ) * δ := by field_simp [hδ_pos.ne'] <;> ring
    _ < (((U.b : ℝ) + 1)) * δ := by gcongr

/-- Two tubes in the same fiber have param L∞ distance < δ. -/
private lemma fiber_param_dist_lt_delta {n : ℕ} {δ : ℝ} (hδ_eq : δ = dyadicDelta n)
    {ℓ1 ℓ2 : AffineLine} {U : DyadicTube n}
    (h1 : snapTube n ℓ1 = U) (h2 : snapTube n ℓ2 = U) :
    dist (tubeSlope ℓ1, tubeIntercept ℓ1) (tubeSlope ℓ2, tubeIntercept ℓ2) < δ := by
  have s1 := snap_slope_in_cell hδ_eq h1
  have s2 := snap_slope_in_cell hδ_eq h2
  have i1 := snap_intercept_in_cell hδ_eq h1
  have i2 := snap_intercept_in_cell hδ_eq h2
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> exact dyadicDelta_pos n
  have hs : |tubeSlope ℓ1 - tubeSlope ℓ2| < δ := by
    have h11 : (U.a : ℝ) * δ ≤ tubeSlope ℓ1 := s1.1
    have h12 : tubeSlope ℓ1 < ((U.a : ℝ) + 1) * δ := s1.2
    have h21 : (U.a : ℝ) * δ ≤ tubeSlope ℓ2 := s2.1
    have h22 : tubeSlope ℓ2 < ((U.a : ℝ) + 1) * δ := s2.2
    rw [abs_lt] <;> constructor <;> linarith
  have hi : |tubeIntercept ℓ1 - tubeIntercept ℓ2| < δ := by
    have h11 : (U.b : ℝ) * δ ≤ tubeIntercept ℓ1 := i1.1
    have h12 : tubeIntercept ℓ1 < ((U.b : ℝ) + 1) * δ := i1.2
    have h21 : (U.b : ℝ) * δ ≤ tubeIntercept ℓ2 := i2.1
    have h22 : tubeIntercept ℓ2 < ((U.b : ℝ) + 1) * δ := i2.2
    rw [abs_lt] <;> constructor <;> linarith
  simp [Prod.dist_eq, max_lt_iff] <;> exact ⟨hs, hi⟩

/-- Fiber size bound: a δ/2-separated family of bounded AffineLines has at most
    `affineLine_packing_constant_720` tubes snapping to the same DyadicTube.

    All tubes in a fiber lie in a δ-cell (param L∞ dist < δ).
    By antilipschitz, line dist < 10δ, so they fit in a 10δ-ball.
    With δ/2 separation > (10δ)/360 = δ/36, packing_bound_720 applies. -/
lemma snap_fiber_bound {n : ℕ} {δ : ℝ} (hδ_eq : δ = dyadicDelta n)
    (T : Finset AffineLine) (U : DyadicTube n)
    (h_sep : SeparatedAt (δ / 2) (T : Set AffineLine))
    (h_v : ∀ ℓ ∈ T, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (h_a : ∀ ℓ ∈ T, |tubeSlope ℓ| ≤ 1)
    (h_b : ∀ ℓ ∈ T, |tubeIntercept ℓ| ≤ 3) :
    (T.filter (fun ℓ => snapTube n ℓ = U)).card ≤
      MainAppendix.affineLine_packing_constant_720 := by
  set fiber := T.filter (fun ℓ => snapTube n ℓ = U) with hfiber_def
  by_cases h_empty : fiber = ∅
  · have h_card : fiber.card = 0 := by rw [h_empty] <;> simp
    rw [h_card]
    <;> exact Nat.zero_le _
  · have h_nonempty : fiber.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨ℓ0, hℓ0⟩
    have hℓ0_in_T : ℓ0 ∈ T := (Finset.mem_filter.mp hℓ0).1
    have h_snap0 : snapTube n ℓ0 = U := (Finset.mem_filter.mp hℓ0).2
    have hδ_pos : 0 < δ := by rw [hδ_eq] <;> exact dyadicDelta_pos n
    have h10δ_pos : 0 < 10 * δ := by positivity
    have h_sub : (fiber : Set AffineLine) ⊆ Metric.closedBall ℓ0 (10 * δ) := by
      intro ℓ hℓ
      have hℓ_in_T : ℓ ∈ T := (Finset.mem_filter.mp hℓ).1
      have h_snap : snapTube n ℓ = U := (Finset.mem_filter.mp hℓ).2
      have h_param : dist (tubeSlope ℓ, tubeIntercept ℓ)
            (tubeSlope ℓ0, tubeIntercept ℓ0) < δ :=
        fiber_param_dist_lt_delta hδ_eq h_snap h_snap0
      have h_antilip : dist ℓ ℓ0 ≤ 10 * dist (tubeSlope ℓ, tubeIntercept ℓ)
            (tubeSlope ℓ0, tubeIntercept ℓ0) :=
        AffineLineLipschitzTransfer.affineLineParams_antilipschitz ℓ ℓ0
          (h_v ℓ hℓ_in_T) (h_v ℓ0 hℓ0_in_T)
          (h_a ℓ hℓ_in_T) (h_a ℓ0 hℓ0_in_T)
          (h_b ℓ hℓ_in_T) (h_b ℓ0 hℓ0_in_T)
      have h_dist : dist ℓ ℓ0 < 10 * δ := by
        calc dist ℓ ℓ0
          ≤ 10 * dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) := h_antilip
        _ < 10 * δ := by gcongr
      exact h_dist.le
    have h_sep' : Set.Pairwise (fiber : Set AffineLine)
        (fun x y => (10 * δ) / 360 ≤ dist x y) := by
      intro x hx y hy hxy
      have h_x_in_T : x ∈ T := (Finset.mem_filter.mp hx).1
      have h_y_in_T : y ∈ T := (Finset.mem_filter.mp hy).1
      have h_sep_xy : δ / 2 ≤ dist x y := h_sep h_x_in_T h_y_in_T hxy
      have h_ineq : (10 * δ) / 360 ≤ δ / 2 := by
        have hδ_pos' : 0 < δ := hδ_pos
        linarith
      linarith
    have h_pack := MainAppendix.affineLine_packing_bound_720 (10 * δ) h10δ_pos h_sep' ℓ0 h_sub
    have h_encard : (fiber : Set AffineLine).encard ≤
        ↑MainAppendix.affineLine_packing_constant_720 := h_pack.2
    have h_eq : (fiber : Set AffineLine).encard = ↑fiber.card := by
      simp
    rw [h_eq] at h_encard
    exact_mod_cast h_encard

/-- BallGrowth transfer: AffineLine → DyadicTube via snapping.

    Given a δ/2-separated, bounded family T with BallGrowth δ s C,
    the snapped family T' = T.image (snapTube n) has
    BallGrowth δ s (C * 40^s * max 1 affineLine_packing_constant_720).

    Proof: pick reference U1 ∈ S', let ℓ0 = f(U1). For any U ∈ S',
    dist(U,U1) ≤ 2r, so dist(ℓ_U, ℓ0) ≤ 10(2δ+2r) ≤ 40r.
    Preimages inject into T ∩ ball(ℓ0, 40r), so BallGrowth applies.
    Fiber bound gives |T| ≤ L · |T'|. -/
lemma ballGrowth_transfer_snap {n : ℕ} {δ s C : ℝ}
    (hδ_eq : δ = dyadicDelta n)
    (T : Finset AffineLine)
    (h_bg : BallGrowth δ s C T)
    (h_sep : SeparatedAt (δ / 2) (T : Set AffineLine))
    (h_v : ∀ ℓ ∈ T, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (h_a : ∀ ℓ ∈ T, |tubeSlope ℓ| ≤ 1)
    (h_b : ∀ ℓ ∈ T, |tubeIntercept ℓ| ≤ 3) :
    BallGrowth δ s
      (C * (40 : ℝ) ^ s * (max 1 (MainAppendix.affineLine_packing_constant_720 : ℝ)))
      (T.image (snapTube n)) := by
  let T' := T.image (snapTube n)
  let L : ℝ := ↑MainAppendix.affineLine_packing_constant_720
  let L' : ℝ := max 1 L
  have hδ_pos : 0 < δ := h_bg.δ_pos
  have hs_nonneg : 0 ≤ s := h_bg.s_nonneg
  have hC_one : 1 ≤ C := h_bg.C_one
  have hT_nonempty : T.Nonempty := h_bg.nonempty
  have hT'_nonempty : T'.Nonempty := Finset.Nonempty.image hT_nonempty _
  have hL'_one : 1 ≤ L' := by simp [L']
  have h40s_one : 1 ≤ (40 : ℝ) ^ s := by
    have h_log : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
    have h_def : (40 : ℝ) ^ s = Real.exp (s * Real.log 40) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      <;> ring_nf
    rw [h_def]
    have h5 : 0 ≤ s * Real.log 40 := by positivity
    have h6 : (1 : ℝ) ≤ Real.exp (s * Real.log 40) := by
      have h7 : Real.exp 0 ≤ Real.exp (s * Real.log 40) := Real.exp_le_exp.mpr h5
      simpa using h7
    exact h6
  have hC'_one : 1 ≤ C * (40 : ℝ) ^ s * L' := by
    have h41 : 1 ≤ C := hC_one
    have h42 : 1 ≤ (40 : ℝ) ^ s := h40s_one
    have h43 : 1 ≤ L' := hL'_one
    have h44 : 1 ≤ C * (40 : ℝ) ^ s := by
      calc 1 = 1 * 1 := by ring
        _ ≤ C * (40 : ℝ) ^ s := by exact mul_le_mul h41 h42 (by positivity) (by positivity)
    calc 1 = 1 * 1 := by ring
      _ ≤ (C * (40 : ℝ) ^ s) * L' := by exact mul_le_mul h44 h43 (by positivity) (by positivity)
      _ = C * (40 : ℝ) ^ s * L' := by ring
  have h_fiber : ∀ U ∈ T', (T.filter (fun ℓ => snapTube n ℓ = U)).card ≤
      MainAppendix.affineLine_packing_constant_720 := by
    intro U hU
    exact snap_fiber_bound hδ_eq T U h_sep h_v h_a h_b
  have h_fiber' : ∀ U ∈ T', ((T.filter (fun ℓ => snapTube n ℓ = U)).card : ℝ) ≤ L' := by
    intro U hU
    have h6 : (T.filter (fun ℓ => snapTube n ℓ = U)).card ≤ MainAppendix.affineLine_packing_constant_720 :=
      h_fiber U hU
    have h7 : (MainAppendix.affineLine_packing_constant_720 : ℝ) ≤ L' := by
      simp [L', L] <;> exact le_max_right _ _
    exact le_trans (mod_cast h6) h7
  have h_disj : ∀ U1 ∈ T', ∀ U2 ∈ T', U1 ≠ U2 →
      Disjoint (T.filter (fun ℓ => snapTube n ℓ = U1))
        (T.filter (fun ℓ => snapTube n ℓ = U2)) := by
    intro U1 _ U2 _ hne
    apply Finset.disjoint_left.mpr
    intro ℓ hℓ1 hℓ2
    have h1 : snapTube n ℓ = U1 := (Finset.mem_filter.mp hℓ1).2
    have h2 : snapTube n ℓ = U2 := (Finset.mem_filter.mp hℓ2).2
    have h3 : U1 = U2 := by
      rw [←h1, h2]
    exact hne h3
  have h_union : (Finset.biUnion T' (fun U => T.filter (fun ℓ => snapTube n ℓ = U))) = T := by
    ext ℓ
    simp [T', Finset.mem_image] <;> tauto
  have h_card_biUnion : (Finset.biUnion T' (fun U => T.filter (fun ℓ => snapTube n ℓ = U))).card =
      ∑ U ∈ T', (T.filter (fun ℓ => snapTube n ℓ = U)).card :=
    Finset.card_biUnion (fun U1 hU1 U2 hU2 hne => h_disj U1 hU1 U2 hU2 hne)
  have h_card_T : T.card = ∑ U ∈ T', (T.filter (fun ℓ => snapTube n ℓ = U)).card := by
    rw [h_union] at h_card_biUnion
    exact h_card_biUnion
  have h_card_T' : (T.card : ℝ) = ∑ U ∈ T', ((T.filter (fun ℓ => snapTube n ℓ = U)).card : ℝ) := by
    exact_mod_cast h_card_T
  have h_card_T_le : (T.card : ℝ) ≤ L' * (T'.card : ℝ) := by
    calc (T.card : ℝ)
      = ∑ U ∈ T', ((T.filter (fun ℓ => snapTube n ℓ = U)).card : ℝ) := h_card_T'
    _ ≤ ∑ U ∈ T', L' := by
        apply Finset.sum_le_sum
        intro U hU
        exact h_fiber' U hU
    _ = L' * (T'.card : ℝ) := by
        simp [Finset.sum_const] <;> ring
  let f : DyadicTube n → AffineLine := fun U =>
    if hU : U ∈ T' then
      Classical.choose (Finset.mem_image.mp hU)
    else
      Classical.choose hT_nonempty
  have hf_mem : ∀ U ∈ T', f U ∈ T := by
    intro U hU
    have h : f U = Classical.choose (Finset.mem_image.mp hU) := by
      simp [f, hU]
    rw [h]
    exact (Classical.choose_spec (Finset.mem_image.mp hU)).1
  have hf_snap : ∀ U ∈ T', snapTube n (f U) = U := by
    intro U hU
    have h : f U = Classical.choose (Finset.mem_image.mp hU) := by
      simp [f, hU]
    rw [h]
    exact (Classical.choose_spec (Finset.mem_image.mp hU)).2
  have h_snap_err_slope : ∀ (ℓ : AffineLine) (U : DyadicTube n),
      snapTube n ℓ = U → |tubeSlope ℓ - U.slope| < δ := by
    intro ℓ U h_snap
    have h9 := (snapTube_param_dist_le_delta n ℓ).1
    simpa [h_snap, hδ_eq] using h9
  have h_snap_err_int : ∀ (ℓ : AffineLine) (U : DyadicTube n),
      snapTube n ℓ = U → |tubeIntercept ℓ - U.intercept| < δ := by
    intro ℓ U h_snap
    have h9 := (snapTube_param_dist_le_delta n ℓ).2
    simpa [h_snap, hδ_eq] using h9
  have h_triangle : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
    intro a b
    exact real_abs_add a b
  have h_line_dist : ∀ (ℓ1 ℓ2 : AffineLine) (U1 U2 : DyadicTube n),
      snapTube n ℓ1 = U1 → snapTube n ℓ2 = U2 →
      ℓ1 ∈ T → ℓ2 ∈ T → dist ℓ1 ℓ2 ≤ 10 * (2 * δ + dist U1 U2) := by
    intro ℓ1 ℓ2 U1 U2 h_snap1 h_snap2 hℓ1 hℓ2
    have h_se1 := h_snap_err_slope ℓ1 U1 h_snap1
    have h_se2 := h_snap_err_slope ℓ2 U2 h_snap2
    have h_ie1 := h_snap_err_int ℓ1 U1 h_snap1
    have h_ie2 := h_snap_err_int ℓ2 U2 h_snap2
    have h_slope_U : |U1.slope - U2.slope| ≤ dist U1 U2 := by
      have hdef : dist U1 U2 = |U1.slope - U2.slope| + |U1.intercept - U2.intercept| := rfl
      rw [hdef]; have hnonneg : 0 ≤ |U1.intercept - U2.intercept| := abs_nonneg _; linarith
    have h_int_U : |U1.intercept - U2.intercept| ≤ dist U1 U2 := by
      have hdef : dist U1 U2 = |U1.slope - U2.slope| + |U1.intercept - U2.intercept| := rfl
      rw [hdef]; have hnonneg : 0 ≤ |U1.slope - U2.slope| := abs_nonneg _; linarith
    have h4 : |tubeSlope ℓ1 - tubeSlope ℓ2| ≤
        |tubeSlope ℓ1 - U1.slope| + |U1.slope - U2.slope| + |U2.slope - tubeSlope ℓ2| := by
      have h6 := h_triangle (tubeSlope ℓ1 - U1.slope) ((U1.slope - U2.slope) + (U2.slope - tubeSlope ℓ2))
      have h7 := h_triangle (U1.slope - U2.slope) (U2.slope - tubeSlope ℓ2)
      calc |tubeSlope ℓ1 - tubeSlope ℓ2|
        = |(tubeSlope ℓ1 - U1.slope) + ((U1.slope - U2.slope) + (U2.slope - tubeSlope ℓ2))| := by ring_nf
      _ ≤ |tubeSlope ℓ1 - U1.slope| + |(U1.slope - U2.slope) + (U2.slope - tubeSlope ℓ2)| := h6
      _ ≤ |tubeSlope ℓ1 - U1.slope| + (|U1.slope - U2.slope| + |U2.slope - tubeSlope ℓ2|) := by gcongr
      _ = |tubeSlope ℓ1 - U1.slope| + |U1.slope - U2.slope| + |U2.slope - tubeSlope ℓ2| := by ring
    have h8 : |tubeIntercept ℓ1 - tubeIntercept ℓ2| ≤
        |tubeIntercept ℓ1 - U1.intercept| + |U1.intercept - U2.intercept| + |U2.intercept - tubeIntercept ℓ2| := by
      have h10 := h_triangle (tubeIntercept ℓ1 - U1.intercept) ((U1.intercept - U2.intercept) + (U2.intercept - tubeIntercept ℓ2))
      have h11 := h_triangle (U1.intercept - U2.intercept) (U2.intercept - tubeIntercept ℓ2)
      calc |tubeIntercept ℓ1 - tubeIntercept ℓ2|
        = |(tubeIntercept ℓ1 - U1.intercept) + ((U1.intercept - U2.intercept) + (U2.intercept - tubeIntercept ℓ2))| := by ring_nf
      _ ≤ |tubeIntercept ℓ1 - U1.intercept| + |(U1.intercept - U2.intercept) + (U2.intercept - tubeIntercept ℓ2)| := h10
      _ ≤ |tubeIntercept ℓ1 - U1.intercept| + (|U1.intercept - U2.intercept| + |U2.intercept - tubeIntercept ℓ2|) := by gcongr
      _ = |tubeIntercept ℓ1 - U1.intercept| + |U1.intercept - U2.intercept| + |U2.intercept - tubeIntercept ℓ2| := by ring
    have h_se2' : |U2.slope - tubeSlope ℓ2| < δ := by
      have h_eq : |U2.slope - tubeSlope ℓ2| = |tubeSlope ℓ2 - U2.slope| := by
        rw [show U2.slope - tubeSlope ℓ2 = -(tubeSlope ℓ2 - U2.slope) by ring, abs_neg]
      rw [h_eq]; exact h_se2
    have h_slope : |tubeSlope ℓ1 - tubeSlope ℓ2| < 2 * δ + dist U1 U2 := by
      calc |tubeSlope ℓ1 - tubeSlope ℓ2|
        ≤ |tubeSlope ℓ1 - U1.slope| + |U1.slope - U2.slope| + |U2.slope - tubeSlope ℓ2| := h4
      _ < 2 * δ + dist U1 U2 := by
        have h1 : |tubeSlope ℓ1 - U1.slope| < δ := h_se1
        have h2 : |U1.slope - U2.slope| ≤ dist U1 U2 := h_slope_U
        have h3 : |U2.slope - tubeSlope ℓ2| < δ := h_se2'
        linarith
    have h_ie2' : |U2.intercept - tubeIntercept ℓ2| < δ := by
      have h_eq : |U2.intercept - tubeIntercept ℓ2| = |tubeIntercept ℓ2 - U2.intercept| := by
        rw [show U2.intercept - tubeIntercept ℓ2 = -(tubeIntercept ℓ2 - U2.intercept) by ring, abs_neg]
      rw [h_eq]; exact h_ie2
    have h_int : |tubeIntercept ℓ1 - tubeIntercept ℓ2| < 2 * δ + dist U1 U2 := by
      calc |tubeIntercept ℓ1 - tubeIntercept ℓ2|
        ≤ |tubeIntercept ℓ1 - U1.intercept| + |U1.intercept - U2.intercept| + |U2.intercept - tubeIntercept ℓ2| := h8
      _ < 2 * δ + dist U1 U2 := by
        have h1 : |tubeIntercept ℓ1 - U1.intercept| < δ := h_ie1
        have h2 : |U1.intercept - U2.intercept| ≤ dist U1 U2 := h_int_U
        have h3 : |U2.intercept - tubeIntercept ℓ2| < δ := h_ie2'
        linarith
    have h_param : dist (tubeSlope ℓ1, tubeIntercept ℓ1) (tubeSlope ℓ2, tubeIntercept ℓ2) < 2 * δ + dist U1 U2 := by
      simp [Prod.dist_eq, max_lt_iff] <;> exact ⟨h_slope, h_int⟩
    have h_antilip : dist ℓ1 ℓ2 ≤ 10 * dist (tubeSlope ℓ1, tubeIntercept ℓ1) (tubeSlope ℓ2, tubeIntercept ℓ2) :=
      AffineLineLipschitzTransfer.affineLineParams_antilipschitz ℓ1 ℓ2
        (h_v ℓ1 hℓ1) (h_v ℓ2 hℓ2) (h_a ℓ1 hℓ1) (h_a ℓ2 hℓ2) (h_b ℓ1 hℓ1) (h_b ℓ2 hℓ2)
    calc dist ℓ1 ℓ2
      ≤ 10 * dist (tubeSlope ℓ1, tubeIntercept ℓ1) (tubeSlope ℓ2, tubeIntercept ℓ2) := h_antilip
    _ ≤ 10 * (2 * δ + dist U1 U2) := by gcongr <;> exact h_param.le
  have h_growth : ∀ (U0 : DyadicTube n) (r : ℝ), δ ≤ r →
      ((T'.filter fun U => dist U U0 ≤ r).card : ℝ) ≤
        (C * (40 : ℝ) ^ s * L') * r ^ s * (T'.card : ℝ) := by
    intro U0 r hr
    set S' := T'.filter (fun U => dist U U0 ≤ r) with hS'_def
    by_cases hS_empty : S' = ∅
    · have h_card0 : (S'.card : ℝ) = 0 := by
        simpa [S', hS_empty] using rfl
      rw [h_card0]
      have h_nonneg : 0 ≤ (C * (40 : ℝ) ^ s * L') * r ^ s * (T'.card : ℝ) := by
        have hr_pos : 0 < r := by linarith
        positivity
      exact h_nonneg
    · rcases Finset.nonempty_iff_ne_empty.mpr hS_empty with ⟨U1, hU1⟩
      have hU1_in_T' : U1 ∈ T' := (Finset.mem_filter.mp hU1).1
      have h_dist_U1 : dist U1 U0 ≤ r := (Finset.mem_filter.mp hU1).2
      let ℓ0 := f U1
      have hℓ0_in_T : ℓ0 ∈ T := hf_mem U1 hU1_in_T'
      let preimages := S'.image f
      have h_inj : Set.InjOn f (S' : Set (DyadicTube n)) := by
        intro V1 hV1 V2 hV2 h
        have h1 : V1 ∈ T' := (Finset.mem_filter.mp hV1).1
        have h2 : V2 ∈ T' := (Finset.mem_filter.mp hV2).1
        have hsnap1 : snapTube n (f V1) = V1 := hf_snap V1 h1
        have hsnap2 : snapTube n (f V2) = V2 := hf_snap V2 h2
        rw [h] at hsnap1
        have h_eq : V1 = V2 := by rw [←hsnap1, hsnap2]
        exact h_eq
      have h_preimages_card : preimages.card = S'.card :=
        Finset.card_image_of_injOn h_inj
      have h_dist_bound : ∀ ℓ ∈ preimages, dist ℓ ℓ0 ≤ 40 * r := by
        intro ℓ hℓ
        rcases Finset.mem_image.mp hℓ with ⟨V, hV, rfl⟩
        have hV_in_T' : V ∈ T' := (Finset.mem_filter.mp hV).1
        have h_dist_V : dist V U0 ≤ r := (Finset.mem_filter.mp hV).2
        have h_dist_VU1 : dist V U1 ≤ 2 * r := by
          calc dist V U1
            ≤ dist V U0 + dist U0 U1 := dist_triangle _ _ _
          _ ≤ dist V U0 + dist U1 U0 := by rw [dist_comm U0 U1]
          _ ≤ r + r := by gcongr
          _ = 2 * r := by ring
        have h_bound := h_line_dist (f V) ℓ0 V U1
          (hf_snap V hV_in_T') (hf_snap U1 hU1_in_T')
          (hf_mem V hV_in_T') hℓ0_in_T
        calc dist (f V) ℓ0
          ≤ 10 * (2 * δ + dist V U1) := h_bound
        _ ≤ 10 * (2 * δ + 2 * r) := by gcongr
        _ = 20 * δ + 20 * r := by ring
        _ ≤ 40 * r := by linarith
      have h_preimages_sub : preimages ⊆ T.filter (fun ℓ => dist ℓ ℓ0 ≤ 40 * r) := by
        intro ℓ hℓ
        have hℓ_in_T : ℓ ∈ T := by
          rcases Finset.mem_image.mp hℓ with ⟨V, hV, rfl⟩
          exact hf_mem V (Finset.mem_filter.mp hV).1
        exact Finset.mem_filter.mpr ⟨hℓ_in_T, h_dist_bound ℓ hℓ⟩
      have h40r_geδ : δ ≤ 40 * r := by linarith
      have h_bg40 := h_bg.growth ℓ0 (40 * r) h40r_geδ
      have h_card_eq : (S'.card : ℝ) = (preimages.card : ℝ) := by
        rw [h_preimages_card]
      calc (S'.card : ℝ)
        = (preimages.card : ℝ) := h_card_eq
      _ ≤ ((T.filter (fun ℓ => dist ℓ ℓ0 ≤ 40 * r)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h_preimages_sub
      _ ≤ C * (40 * r) ^ s * (T.card : ℝ) := h_bg40
      _ = C * (40 : ℝ) ^ s * r ^ s * (T.card : ℝ) := by
          have hpow : (40 * r) ^ s = (40 : ℝ) ^ s * r ^ s := by
            rw [Real.mul_rpow (by norm_num) (by linarith)]
          rw [hpow] <;> ring
      _ ≤ C * (40 : ℝ) ^ s * r ^ s * (L' * (T'.card : ℝ)) := by
          have h_goal : (T.card : ℝ) ≤ L' * (T'.card : ℝ) := h_card_T_le
          have h_pos : 0 ≤ C * (40 : ℝ) ^ s * r ^ s := by
            have hr_pos' : 0 < r := by linarith
            have hC_pos : 0 < C := by linarith
            have h40s_pos : 0 < (40 : ℝ) ^ s := by positivity
            have hrs_pos : 0 < r ^ s := by positivity
            positivity
          nlinarith
      _ = (C * (40 : ℝ) ^ s * L') * r ^ s * (T'.card : ℝ) := by ring
  exact ⟨hT'_nonempty, hδ_pos, hC'_one, hs_nonneg, h_growth⟩

/-! ========================================================================
   6. Output conversion helpers
   ======================================================================== -/

/-- Convert dyadic coarse tube family to AffineLine in A2 convention. -/
def coarseToAffine {m : ℕ} (C : Finset (DyadicTube m)) : Finset CoarseTube :=
  C.image dyadicTubeToA2

/-- Convert dyadic fine tube family to AffineLine in A2 convention. -/
def fineToAffine {n : ℕ} (T_dyadic : Plane → Finset (DyadicTube n)) :
    Plane → Finset FineTube :=
  fun p => (T_dyadic p).image dyadicTubeToA2

/-! ========================================================================
   7. Dyadic QTTC wrapper for A2 integration
   ======================================================================== -/

/-- Select one preimage per snapped tube.

    Given `V ∈ T_dyadic p` where `T_dyadic p = (T p).image (snapTube n)`,
    choose an `ℓ ∈ T p` such that `snapTube n ℓ = V`.
    The selection is injective: if V1 ≠ V2, the selected ℓ1 ≠ ℓ2. -/
def selectPreimage {n : ℕ} (T : Finset AffineLine) (V : DyadicTube n)
    (hV : V ∈ T.image (snapTube n)) : AffineLine :=
  Classical.choose (Finset.mem_image.mp hV)

lemma selectPreimage_spec {n : ℕ} (T : Finset AffineLine) (V : DyadicTube n)
    (hV : V ∈ T.image (snapTube n)) :
    selectPreimage T V hV ∈ T ∧ snapTube n (selectPreimage T V hV) = V :=
  Classical.choose_spec (Finset.mem_image.mp hV)

lemma selectPreimage_injective {n : ℕ} (T : Finset AffineLine)
    (hV1 : ∀ V, V ∈ T.image (snapTube n)) :
    Function.Injective (fun V : DyadicTube n => selectPreimage T V (hV1 V)) := by
  intro V1 V2 h
  have h_eq : selectPreimage T V1 (hV1 V1) = selectPreimage T V2 (hV1 V2) := h
  have h1 : snapTube n (selectPreimage T V1 (hV1 V1)) = V1 :=
    (selectPreimage_spec T V1 (hV1 V1)).2
  have h2 : snapTube n (selectPreimage T V2 (hV1 V2)) = V2 :=
    (selectPreimage_spec T V2 (hV1 V2)).2
  have h3 : snapTube n (selectPreimage T V1 (hV1 V1)) =
           snapTube n (selectPreimage T V2 (hV1 V2)) := by
    rw [h_eq]
  rw [h1, h2] at h3
  exact h3

/-- For dyadic scales, if input tubes have |slope| ≤ 1, then all coarse
    parent tubes in globalCoarseG also have |slope| ≤ 1. -/
lemma globalCoarseG_slope_bound {n m : ℕ} (hnm : m ≤ n)
    (P : Finset Plane) (T : Plane → Finset AffineLine)
    (h_slope : ∀ p ∈ P, ∀ ℓ ∈ T p, |tubeSlope ℓ| ≤ 1) :
    ∀ U ∈ globalCoarseG hnm P (fun p => (T p).image (snapTube n)), |U.slope| ≤ 1 := by
  intro U hU
  rcases Finset.mem_image.mp hU with ⟨V, hV, rfl⟩
  rcases Finset.mem_biUnion.mp hV with ⟨p, hp, hVp⟩
  rcases Finset.mem_image.mp hVp with ⟨ℓ, hℓ, rfl⟩
  have h_a_bound : |tubeSlope ℓ| ≤ 1 := (h_slope p hp ℓ hℓ)
  set V' := snapTube n ℓ with hV'
  set k : ℤ := ↑(refinementFactor n m) with hk
  have hk_pos : 0 < k := refinementFactor_pos' hnm
  have hk_eq : (k : ℝ) = (2 : ℝ)^(n - m) := by
    simp [hk, refinementFactor] <;> norm_cast
  have h1 : -(2 : ℤ)^n ≤ V'.a := by
    have h2 : tubeSlope ℓ ≥ -1 := by linarith [abs_le.mp h_a_bound]
    have h3 : tubeSlope ℓ / dyadicDelta n ≥ -(2 : ℝ)^n := by
      have h4 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> norm_cast
      rw [h4]; have h5 : 0 < (2 : ℝ)^n := by positivity
      field_simp [h5.ne'] <;> linarith
    have h6 : (-(2 : ℤ)^n : ℝ) ≤ tubeSlope ℓ / dyadicDelta n := by exact_mod_cast h3
    have h7 : (-(2 : ℤ)^n : ℝ) ≤ (V'.a : ℝ) := by
      have h8 : (V'.a : ℝ) = ⌊tubeSlope ℓ / dyadicDelta n⌋ := by
        simp [V', snapTube, DyadicTube.a] <;> norm_cast <;> rfl
      rw [h8]
      have h9 : (⌊tubeSlope ℓ / dyadicDelta n⌋ : ℝ) ≤ tubeSlope ℓ / dyadicDelta n := Int.floor_le _
      have h10 : (-(2 : ℤ)^n : ℝ) ≤ (⌊tubeSlope ℓ / dyadicDelta n⌋ : ℝ) := by
        have h6' : (↑(-(2 : ℤ)^n) : ℝ) ≤ tubeSlope ℓ / dyadicDelta n := by simpa using h6
        have h11 : (-(2 : ℤ)^n) ≤ ⌊tubeSlope ℓ / dyadicDelta n⌋ := (Int.le_floor (z := (-(2 : ℤ)^n))).mpr h6'
        exact_mod_cast h11
      exact h10
    exact_mod_cast h7
  have h2 : V'.a ≤ (2 : ℤ)^n := by
    have h3 : tubeSlope ℓ ≤ 1 := by linarith [abs_le.mp h_a_bound]
    have h4 : tubeSlope ℓ / dyadicDelta n ≤ (2 : ℝ)^n := by
      have h5 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> norm_cast
      rw [h5]; have h6 : 0 < (2 : ℝ)^n := by positivity
      field_simp [h6.ne'] <;> linarith
    have h7 : (V'.a : ℝ) ≤ ((2 : ℤ)^n : ℝ) := by
      have h8 : (V'.a : ℝ) = ⌊tubeSlope ℓ / dyadicDelta n⌋ := by
        simp [V', snapTube, DyadicTube.a] <;> norm_cast <;> rfl
      rw [h8]
      have h9 : (⌊tubeSlope ℓ / dyadicDelta n⌋ : ℝ) ≤ tubeSlope ℓ / dyadicDelta n := Int.floor_le _
      linarith
    exact_mod_cast h7
  set U' := sourceParent hnm V' with hU'
  have h_mul_upper : V'.a ≤ (2 : ℤ)^m * k := by
    have h_eq : (2 : ℤ)^m * k = (2 : ℤ)^n := by
      have h : (k : ℤ) = (2 : ℤ)^(n - m) := by
        simp [hk, refinementFactor] <;> norm_cast
      rw [h]
      have h2 : n = m + (n - m) := by omega
      rw [h2]
      simp [pow_add] <;> ring
    rw [h_eq]
    exact h2
  have h_mul_lower : (-(2 : ℤ)^m) * k ≤ V'.a := by
    have h_eq : (-(2 : ℤ)^m) * k = -(2 : ℤ)^n := by
      have h : (k : ℤ) = (2 : ℤ)^(n - m) := by
        simp [hk, refinementFactor] <;> norm_cast
      rw [h]
      have h2 : n = m + (n - m) := by omega
      rw [h2]
      simp [pow_add] <;> ring
    rw [h_eq]
    exact h1
  have h3 : -(2 : ℤ)^m ≤ U'.a := by
    have h4 : U'.a = V'.a / k := by
      simp [U', hU', sourceParent, coarseTubeToM] <;> rfl
    rw [h4]
    exact Int.le_ediv_of_mul_le hk_pos h_mul_lower
  have h4 : U'.a ≤ (2 : ℤ)^m := by
    have h5 : U'.a = V'.a / k := by
      simp [U', hU', sourceParent, coarseTubeToM] <;> rfl
    rw [h5]
    exact Int.ediv_le_of_le_mul hk_pos h_mul_upper
  have h5 : |U'.slope| ≤ 1 := by
    have h6 : U'.slope = (U'.a : ℝ) * dyadicDelta m := by
      simp [DyadicTube.slope] <;> ring
    rw [h6]
    have h7 : dyadicDelta m = 1 / (2 : ℝ)^m := by simp [dyadicDelta] <;> norm_cast
    rw [h7]
    have h8 : -(1 : ℝ) ≤ (U'.a : ℝ) * (1 / (2 : ℝ)^m) := by
      have h9 : (U'.a : ℝ) ≥ -(2 : ℝ)^m := by exact_mod_cast h3
      have h10 : 0 < (2 : ℝ)^m := by positivity
      have h11 : (U'.a : ℝ) * (1 / (2 : ℝ)^m) ≥ (-(2 : ℝ)^m) * (1 / (2 : ℝ)^m) := by
        exact mul_le_mul_of_nonneg_right h9 (by positivity)
      have h12 : (-(2 : ℝ)^m) * (1 / (2 : ℝ)^m) = -1 := by
        field_simp [h10.ne'] <;> ring
      linarith
    have h11 : (U'.a : ℝ) * (1 / (2 : ℝ)^m) ≤ 1 := by
      have h12 : (U'.a : ℝ) ≤ (2 : ℝ)^m := by exact_mod_cast h4
      have h13 : 0 < (2 : ℝ)^m := by positivity
      have h14 : (U'.a : ℝ) * (1 / (2 : ℝ)^m) ≤ (2 : ℝ)^m * (1 / (2 : ℝ)^m) := by
        exact mul_le_mul_of_nonneg_right h12 (by positivity)
      have h15 : (2 : ℝ)^m * (1 / (2 : ℝ)^m) = 1 := by
        field_simp [h13.ne'] <;> ring
      linarith
    rw [abs_le] <;> constructor <;> linarith
  exact h5

/-- For dyadic scales, if input tubes have |intercept| ≤ 2, then all coarse
    parent tubes in globalCoarseG have |intercept| ≤ 3. -/
lemma globalCoarseG_intercept_bound {n m : ℕ} (hnm : m ≤ n) (hm_pos : 1 ≤ m)
    (P : Finset Plane) (T : Plane → Finset AffineLine)
    (h_intercept : ∀ p ∈ P, ∀ ℓ ∈ T p, |tubeIntercept ℓ| ≤ 2) :
    ∀ U ∈ globalCoarseG hnm P (fun p => (T p).image (snapTube n)), |U.intercept| ≤ 3 := by
  intro U hU
  rcases Finset.mem_image.mp hU with ⟨V, hV, rfl⟩
  rcases Finset.mem_biUnion.mp hV with ⟨p, hp, hVp⟩
  rcases Finset.mem_image.mp hVp with ⟨ℓ, hℓ, rfl⟩
  have h_b_bound : |tubeIntercept ℓ| ≤ 2 := (h_intercept p hp ℓ hℓ)
  set V' := snapTube n ℓ with hV'
  set k : ℤ := ↑(refinementFactor n m) with hk
  have hk_pos : 0 < k := refinementFactor_pos' hnm
  have h_k_eq : (k : ℤ) = (2 : ℤ)^(n - m) := by
    simp [hk, refinementFactor] <;> norm_cast
  have h_pow_mul : (2 : ℤ)^m * k = (2 : ℤ)^n := by
    rw [h_k_eq]
    have h2 : m + (n - m) = n := by omega
    have h3 : (2 : ℤ)^m * (2 : ℤ)^(n - m) = (2 : ℤ)^(m + (n - m)) := by
      rw [← pow_add]
    rw [h3, h2]
  have h1 : -2 * (2 : ℤ)^n - 1 ≤ V'.b := by
    have h2 : tubeIntercept ℓ ≥ -2 := by linarith [abs_le.mp h_b_bound]
    have h3 : tubeIntercept ℓ / dyadicDelta n ≥ -2 * (2 : ℝ)^n := by
      have h4 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> norm_cast
      rw [h4]; have h5 : 0 < (2 : ℝ)^n := by positivity
      field_simp [h5.ne'] <;> linarith
    have h6 : (V'.b : ℝ) = ⌊tubeIntercept ℓ / dyadicDelta n⌋ := by
      simp [V', snapTube, DyadicTube.b] <;> norm_cast <;> rfl
    have h7 : (V'.b : ℝ) ≥ -2 * (2 : ℝ)^n - 1 := by
      rw [h6]
      have h8 : (⌊tubeIntercept ℓ / dyadicDelta n⌋ : ℝ) ≥ tubeIntercept ℓ / dyadicDelta n - 1 := by
        linarith [Int.floor_le (tubeIntercept ℓ / dyadicDelta n), Int.lt_floor_add_one (tubeIntercept ℓ / dyadicDelta n)]
      linarith
    have h9 : (-2 * (2 : ℤ)^n - 1 : ℝ) = -2 * (2 : ℝ)^n - 1 := by
      simp [mul_comm] <;> ring
    rw [h9] at *
    exact_mod_cast h7
  have h2 : V'.b ≤ 2 * (2 : ℤ)^n := by
    have h3 : tubeIntercept ℓ ≤ 2 := by linarith [abs_le.mp h_b_bound]
    have h4 : tubeIntercept ℓ / dyadicDelta n ≤ 2 * (2 : ℝ)^n := by
      have h5 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> norm_cast
      rw [h5]; have h6 : 0 < (2 : ℝ)^n := by positivity
      field_simp [h6.ne'] <;> linarith
    have h7 : (V'.b : ℝ) = ⌊tubeIntercept ℓ / dyadicDelta n⌋ := by
      simp [V', snapTube, DyadicTube.b] <;> norm_cast <;> rfl
    have h8 : (V'.b : ℝ) ≤ 2 * (2 : ℝ)^n := by
      rw [h7]
      have h9 : (⌊tubeIntercept ℓ / dyadicDelta n⌋ : ℝ) ≤ tubeIntercept ℓ / dyadicDelta n := Int.floor_le _
      linarith
    have h10 : (2 * (2 : ℤ)^n : ℝ) = 2 * (2 : ℝ)^n := by
      simp [mul_comm] <;> ring
    rw [h10] at *
    exact_mod_cast h8
  set U' := sourceParent hnm V' with hU'
  have h_mul_upper : V'.b ≤ (2 * (2 : ℤ)^m) * k := by
    calc V'.b ≤ 2 * (2 : ℤ)^n := h2
      _ = 2 * ((2 : ℤ)^m * k) := by rw [h_pow_mul]
      _ = (2 * (2 : ℤ)^m) * k := by ring
  have h_mul_lower : (-(2 * (2 : ℤ)^m) - 1) * k ≤ V'.b := by
    calc (-(2 * (2 : ℤ)^m) - 1) * k
      = -2 * ((2 : ℤ)^m * k) - k := by ring
      _ = -2 * (2 : ℤ)^n - k := by rw [h_pow_mul]
      _ ≤ -2 * (2 : ℤ)^n - 1 := by
        have h_k1 : k ≥ 1 := by linarith [hk_pos]
        nlinarith
      _ ≤ V'.b := h1
  have h3 : -(2 * (2 : ℤ)^m) - 1 ≤ U'.b := by
    have h4 : U'.b = V'.b / k := by
      simp [U', hU', sourceParent, coarseTubeToM] <;> rfl
    rw [h4]
    exact Int.le_ediv_of_mul_le hk_pos h_mul_lower
  have h4 : U'.b ≤ 2 * (2 : ℤ)^m := by
    have h5 : U'.b = V'.b / k := by
      simp [U', hU', sourceParent, coarseTubeToM] <;> rfl
    rw [h5]
    exact Int.ediv_le_of_le_mul hk_pos h_mul_upper
  have h5 : |U'.intercept| ≤ 3 := by
    have h6 : U'.intercept = (U'.b : ℝ) * dyadicDelta m := by
      simp [DyadicTube.intercept] <;> ring
    rw [h6]
    have h7 : dyadicDelta m = 1 / (2 : ℝ)^m := by simp [dyadicDelta] <;> norm_cast
    rw [h7]
    have h10 : 0 < (2 : ℝ)^m := by positivity
    have h_half : 1 / (2 : ℝ)^m ≤ 1 := by
      have h11 : 1 ≤ (2 : ℝ)^m := by
        have h_base : (1 : ℝ) ≤ 2 := by norm_num
        have h112 : (2 : ℝ)^m ≥ (1 : ℝ)^m := by gcongr
        have h113 : (1 : ℝ)^m = 1 := one_pow m
        rw [h113] at h112
        exact h112
      have h12 : 1 / (2 : ℝ)^m ≤ 1 / 1 := by gcongr
      simpa using h12
    have h_lower : -(3 : ℝ) ≤ (U'.b : ℝ) * (1 / (2 : ℝ)^m) := by
      have h9 : (U'.b : ℝ) ≥ -(2 * (2 : ℝ)^m) - 1 := by exact_mod_cast h3
      have h13 : (U'.b : ℝ) * (1 / (2 : ℝ)^m) ≥ (-(2 * (2 : ℝ)^m) - 1) * (1 / (2 : ℝ)^m) := by
        exact mul_le_mul_of_nonneg_right h9 (by positivity)
      have h14 : (-(2 * (2 : ℝ)^m) - 1) * (1 / (2 : ℝ)^m) = -2 - 1 / (2 : ℝ)^m := by
        field_simp [h10.ne'] <;> ring
      have h15 : -2 - 1 / (2 : ℝ)^m ≥ -3 := by
        have h16 : 1 / (2 : ℝ)^m ≤ 1 := h_half
        linarith
      linarith
    have h_upper : (U'.b : ℝ) * (1 / (2 : ℝ)^m) ≤ 3 := by
      have h12 : (U'.b : ℝ) ≤ 2 * (2 : ℝ)^m := by exact_mod_cast h4
      have h13 : (U'.b : ℝ) * (1 / (2 : ℝ)^m) ≤ (2 * (2 : ℝ)^m) * (1 / (2 : ℝ)^m) := by
        exact mul_le_mul_of_nonneg_right h12 (by positivity)
      have h14 : (2 * (2 : ℝ)^m) * (1 / (2 : ℝ)^m) = 2 := by
        field_simp [h10.ne'] <;> ring
      rw [h14] at h13
      linarith
    rw [abs_le] <;> constructor <;> linarith
  exact h5


end DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
