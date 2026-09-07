module

/-
  H2 Migration Adapters: bridge between assignedCountDyadic and assignedCountMetric.

  Provides:
  - floor_eq_imp_abs_lt_one: equal floor → |x-y| < 1
  - sameCell_paramDist_lt_delta: same parent cell → param dist < Δ
  - inParent_dist_lt_tenDelta: InParent → dist < 10Δ
  - assignedCountDyadic_le_assignedCount10: dyadic count ≤ metric count at 10Δ
  - assignedCountDyadic_upper: per-coarse upper bound via ball growth at 10Δ
  - assignedCountDyadic_upper_eps: simplified bound with Δ^{-s-6ε} target
  - pointFiber_partition_single / _global: disjoint fiber partition identities
  - allParentCells / canonicalRepOfCell: cell-based canonical representatives
  - pointFiber_perPoint_partition / _total_partition: cell-based partitions
  - dyadic_bin_pigeonhole: weighted dyadic-bin pigeonhole lemma
  - parentCell_ball_containment: cell-index distance → line distance bound

  Whiteprint node: HeavySquaresRedesign / H2_Migration
  Dependencies: Interfaces, A9_Helpers, AffineLineLipschitzTransfer, QTTC
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.H2Migration

open LemmaE
open TubesAndSlopes
open AffineLineLipschitzTransfer

/-! ========================================================================
   Adapter 0: Geometric bridge InParent → InCoarseTube(10Δ)
   ======================================================================== -/

/-- Helper: equal floor implies |x - y| < 1.
    Both x, y ∈ [k, k+1), so their difference is strictly < 1. -/
lemma floor_eq_imp_abs_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  let k : ℤ := ⌊x⌋
  have hk : ⌊y⌋ = k := h.symm
  have h1 : (k : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (k : ℝ) ≤ y := by
    have h3a : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    rw [hk] at h3a
    exact h3a
  have h4 : y < (k : ℝ) + 1 := by
    have h4a : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [hk] at h4a
    exact h4a
  have h5 : x - y < 1 := by linarith
  have h6 : y - x < 1 := by linarith
  rw [abs_lt] <;> constructor <;> linarith

/-- If two tubes share a dyadic Δ-cell (floor), their parameter distance is < Δ.
    Equal floor(x/Δ) gives |x/Δ - y/Δ| < 1, hence |x - y| < Δ. -/
lemma sameCell_paramDist_lt_delta (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T U : FineTube) (h : InParent Δ hΔ_pos T U) :
    dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < Δ := by
  let aT := tubeSlope T
  let bT := tubeIntercept T
  let aU := tubeSlope U
  let bU := tubeIntercept U
  have hΔ_ne : Δ ≠ 0 := hΔ_pos.ne'
  have h_cell1 : ⌊aT / Δ⌋ = ⌊aU / Δ⌋ := by
    simpa [parentCell, InParent] using congr_arg Prod.fst h
  have h_cell2 : ⌊bT / Δ⌋ = ⌊bU / Δ⌋ := by
    simpa [parentCell, InParent] using congr_arg Prod.snd h
  have ha : |aT - aU| < Δ := by
    have h3 : |aT / Δ - aU / Δ| < 1 := floor_eq_imp_abs_lt_one h_cell1
    have h4 : |aT - aU| = Δ * |aT / Δ - aU / Δ| := by
      have h5 : aT - aU = Δ * (aT / Δ - aU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h5, abs_mul, abs_of_pos hΔ_pos]
    rw [h4]; nlinarith
  have hb : |bT - bU| < Δ := by
    have h3 : |bT / Δ - bU / Δ| < 1 := floor_eq_imp_abs_lt_one h_cell2
    have h4 : |bT - bU| = Δ * |bT / Δ - bU / Δ| := by
      have h5 : bT - bU = Δ * (bT / Δ - bU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h5, abs_mul, abs_of_pos hΔ_pos]
    rw [h4]; nlinarith
  have h_main : dist (aT, bT) (aU, bU) = max (|aT - aU|) (|bT - bU|) := by
    simp [Prod.dist_eq] <;> rfl
  rw [h_main]
  exact max_lt ha hb

/-- Geometric adapter: InParent implies dist < 10*Δ.

    Uses affineLineParams_antilipschitz: dist(line) ≤ 10 * dist(params).
    Same cell gives dist(params) < Δ, hence dist(line) < 10Δ. -/
lemma inParent_dist_lt_tenDelta (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T : FineTube) (U : CoarseTube) (h : InParent Δ hΔ_pos T U)
    (hvT : (getDirV T) 1 ≠ 0) (hvU : (getDirV U) 1 ≠ 0)
    (haT : |tubeSlope T| ≤ 1) (haU : |tubeSlope U| ≤ 1)
    (hbT : |tubeIntercept T| ≤ 3) (hbU : |tubeIntercept U| ≤ 3) :
    dist T U < 10 * Δ := by
  have h_param : dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < Δ :=
    sameCell_paramDist_lt_delta Δ hΔ_pos T U h
  have h_antilipschitz : dist T U ≤ 10 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) :=
    affineLineParams_antilipschitz T U hvT hvU haT haU hbT hbU
  calc dist T U
    ≤ 10 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) := h_antilipschitz
  _ < 10 * Δ := by
    have h7 : 10 * dist (tubeSlope T, tubeIntercept T) (tubeSlope U, tubeIntercept U) < 10 * Δ :=
      mul_lt_mul_of_pos_left h_param (by norm_num)
    linarith

/-! ========================================================================
   Adapter 1: assignedCountDyadic ≤ assignedCount(10Δ)
   ======================================================================== -/

/-- Dyadic assigned count ≤ metric assigned count at threshold 10Δ,
    assuming all tubes satisfy slope/intercept bounds. -/
lemma assignedCountDyadic_le_assignedCount10
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T : Plane → Finset FineTube) (p : Plane) (U : CoarseTube)
    (h_bounds : ∀ T_fine ∈ T p,
      (getDirV T_fine) 1 ≠ 0 ∧ |tubeSlope T_fine| ≤ 1 ∧ |tubeIntercept T_fine| ≤ 3)
    (hvU : (getDirV U) 1 ≠ 0)
    (haU : |tubeSlope U| ≤ 1)
    (hbU : |tubeIntercept U| ≤ 3) :
    assignedCountDyadic Δ hΔ_pos T p U ≤ assignedCountMetric (10 * Δ) T p U := by
  apply Finset.card_le_card
  intro T_fine hT_fine
  have h1 : T_fine ∈ T p := (Finset.mem_filter.mp hT_fine).1
  have h2 : InParent Δ hΔ_pos T_fine U := (Finset.mem_filter.mp hT_fine).2
  have h_bounds' := h_bounds T_fine h1
  have h_dist : dist T_fine U < 10 * Δ :=
    inParent_dist_lt_tenDelta Δ hΔ_pos T_fine U h2
      h_bounds'.1 hvU h_bounds'.2.1 haU h_bounds'.2.2 hbU
  have h3 : InCoarseTube (10 * Δ) T_fine U := by
    simpa [InCoarseTube] using h_dist.le
  exact Finset.mem_filter.mpr ⟨h1, h3⟩

/-! ========================================================================
   Adapter 2: Per-coarse upper bound for assignedCountDyadic
   ======================================================================== -/

/-- Upper bound on dyadic assigned count via ball growth at radius 10Δ.

    If T(p) has ball-growth at scale δ with constant C₁, and |T(p)| ≤ M,
    then assignedCountDyadic ≤ C₁ * (10Δ)^s * |T(p)|.

    With C₁*M ≤ Δ^{-2s-6ε}, this gives ≤ 10^s * Δ^{-s-6ε}. -/
lemma assignedCountDyadic_upper
    (δ Δ s ε C₁ M : ℝ) (p : Plane)
    (T : Plane → Finset FineTube) (T_Q : Plane → Finset FineTube) (U : CoarseTube)
    (hδ_le_Δ : δ ≤ Δ) (hΔ_pos : 0 < Δ)
    (h_finite : BallGrowth δ s C₁ (T p))
    (hT_Q_sub : T_Q p ⊆ T p)
    (h_card : ((T p).card : ℝ) ≤ M)
    (h_bounds : ∀ T_fine ∈ T p,
      (getDirV T_fine) 1 ≠ 0 ∧ |tubeSlope T_fine| ≤ 1 ∧ |tubeIntercept T_fine| ≤ 3)
    (hvU : (getDirV U) 1 ≠ 0)
    (haU : |tubeSlope U| ≤ 1)
    (hbU : |tubeIntercept U| ≤ 3) :
    (assignedCountDyadic Δ hΔ_pos T_Q p U : ℝ) ≤
      C₁ * (10 * Δ) ^ s * (T p).card := by
  have h1 : assignedCountDyadic Δ hΔ_pos T_Q p U ≤ assignedCountMetric (10 * Δ) T_Q p U :=
    assignedCountDyadic_le_assignedCount10 Δ hΔ_pos T_Q p U
      (fun T_fine hT => h_bounds T_fine (hT_Q_sub hT)) hvU haU hbU
  have h2 : assignedCountMetric (10 * Δ) T_Q p U ≤ ((T p).filter (fun ℓ => dist ℓ U ≤ 10 * Δ)).card := by
    apply Finset.card_le_card
    intro ℓ hℓ
    have h3 : ℓ ∈ T_Q p := (Finset.mem_filter.mp hℓ).1
    have h4 : ℓ ∈ T p := hT_Q_sub h3
    have h5 : dist ℓ U ≤ 10 * Δ := (Finset.mem_filter.mp hℓ).2
    exact Finset.mem_filter.mpr ⟨h4, h5⟩
  have h3 : (((T p).filter (fun ℓ => dist ℓ U ≤ 10 * Δ)).card : ℝ) ≤
      C₁ * (10 * Δ) ^ s * (T p).card := by
    have h4 : δ ≤ 10 * Δ := by linarith
    exact h_finite.growth U (10 * Δ) h4
  have h4 : (assignedCountDyadic Δ hΔ_pos T_Q p U : ℝ) ≤
      (((T p).filter (fun ℓ => dist ℓ U ≤ 10 * Δ)).card : ℝ) := by
    exact_mod_cast le_trans h1 h2
  exact le_trans h4 h3

/-! ========================================================================
   Adapter 3: Simplified upper bound with Δ^{-s-6ε} target
   ======================================================================== -/

/-- Dyadic assigned count ≤ 10^s * Δ^{-s-6ε}.

    Uses C₁*M ≤ Δ^{-2s-6ε} and ball growth at 10Δ. -/
lemma assignedCountDyadic_upper_eps
    (δ Δ s ε C₁ M : ℝ) (p : Plane)
    (T : Plane → Finset FineTube) (T_Q : Plane → Finset FineTube) (U : CoarseTube)
    (hδ_le_Δ : δ ≤ Δ) (hΔ_pos : 0 < Δ)
    (h_finite : BallGrowth δ s C₁ (T p))
    (hT_Q_sub : T_Q p ⊆ T p)
    (h_card : ((T p).card : ℝ) ≤ M)
    (hM_upper : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε))
    (hs_nonneg : 0 ≤ s)
    (h_bounds : ∀ T_fine ∈ T p,
      (getDirV T_fine) 1 ≠ 0 ∧ |tubeSlope T_fine| ≤ 1 ∧ |tubeIntercept T_fine| ≤ 3)
    (hvU : (getDirV U) 1 ≠ 0)
    (haU : |tubeSlope U| ≤ 1)
    (hbU : |tubeIntercept U| ≤ 3) :
    (assignedCountDyadic Δ hΔ_pos T_Q p U : ℝ) ≤
      (10 : ℝ) ^ s * Real.rpow Δ (-s - 6 * ε) := by
  have h_main : (assignedCountDyadic Δ hΔ_pos T_Q p U : ℝ) ≤
      C₁ * (10 * Δ) ^ s * (T p).card :=
    assignedCountDyadic_upper δ Δ s ε C₁ M p T T_Q U hδ_le_Δ hΔ_pos
      h_finite hT_Q_sub h_card h_bounds hvU haU hbU
  have hC1 : 0 ≤ C₁ := by
    have h : 1 ≤ C₁ := h_finite.C_one
    linarith
  have hΔs : 0 ≤ (10 * Δ) ^ s := by positivity
  have hpos : 0 ≤ C₁ * (10 * Δ) ^ s := mul_nonneg hC1 hΔs
  have h4 : C₁ * (10 * Δ) ^ s * ((T p).card : ℝ) ≤ C₁ * (10 * Δ) ^ s * M :=
    mul_le_mul_of_nonneg_left h_card hpos
  have h5 : (10 * Δ) ^ s = (10 : ℝ) ^ s * Δ ^ s := by
    rw [Real.mul_rpow (by norm_num) hΔ_pos.le]
    <;> ring
  calc (assignedCountDyadic Δ hΔ_pos T_Q p U : ℝ)
    ≤ C₁ * (10 * Δ) ^ s * ↑((T p).card) := h_main
  _ ≤ C₁ * (10 * Δ) ^ s * M := h4
  _ = (C₁ * M) * (10 * Δ) ^ s := by ring
  _ ≤ Real.rpow Δ (-2 * s - 6 * ε) * (10 * Δ) ^ s := by gcongr
  _ = Real.rpow Δ (-2 * s - 6 * ε) * ((10 : ℝ) ^ s * Δ ^ s) := by rw [h5]
  _ = (10 : ℝ) ^ s * (Real.rpow Δ (-2 * s - 6 * ε) * Δ ^ s) := by ring
  _ = (10 : ℝ) ^ s * Real.rpow Δ (-s - 6 * ε) := by
    have h7 : Real.rpow Δ (-2 * s - 6 * ε) * Δ ^ s = Real.rpow Δ (-s - 6 * ε) := by
      have h8 : Δ ^ s = Real.rpow Δ s := by rfl
      rw [h8]
      have h9 : Real.rpow Δ (-2 * s - 6 * ε) * Real.rpow Δ s =
          Real.rpow Δ ((-2 * s - 6 * ε) + s) :=
        (Real.rpow_add hΔ_pos (-2 * s - 6 * ε) s).symm
      rw [h9]
      have h10 : (-2 * s - 6 * ε) + s = -s - 6 * ε := by ring
      rw [h10]
    rw [h7] <;> ring

/-! ========================================================================
   Adapter 3: PointFiber partition identity (critical for A2 H2 redesign)
   ======================================================================== -/

/-- Single-point partition: if C contains one representative per occupied parent cell,
    then Σ_{U ∈ C} |pointFiber(p,U)| = |T_Q p|. -/
lemma pointFiber_partition_single
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (T_Q : Plane → Finset FineTube) (p : Plane)
    (C : Finset CoarseTube)
    (h_inj : Set.InjOn (parentCell Δ hΔ_pos) (C : Set CoarseTube))
    (h_cover : ∀ T_fine ∈ T_Q p, ∃ U ∈ C, InParent Δ hΔ_pos T_fine U) :
    ∑ U ∈ C, (pointFiber Δ hΔ_pos T_Q p U).card = (T_Q p).card := by
  let f (U : CoarseTube) : Finset FineTube := pointFiber Δ hΔ_pos T_Q p U
  have h_disj : ∀ U1 ∈ C, ∀ U2 ∈ C, U1 ≠ U2 → Disjoint (f U1) (f U2) := by
    intro U1 hU1 U2 hU2 hne
    have h_cells_ne : parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 := by
      intro h_eq
      exact hne (h_inj hU1 hU2 h_eq)
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h_in1 : InParent Δ hΔ_pos x U1 := (Finset.mem_filter.mp hx1).2
    have h_in2 : InParent Δ hΔ_pos x U2 := (Finset.mem_filter.mp hx2).2
    have h_eq : parentCell Δ hΔ_pos U1 = parentCell Δ hΔ_pos U2 := by
      dsimp only [InParent] at h_in1 h_in2
      exact h_in1.symm.trans h_in2
    exact h_cells_ne h_eq
  have h_union : (C.biUnion f) = T_Q p := by
    ext x
    simp only [Finset.mem_biUnion, f, pointFiber]
    constructor
    · rintro ⟨U, _, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      rcases h_cover x hx with ⟨U, hU, h_in⟩
      exact ⟨U, hU, by simpa [f, pointFiber, Finset.mem_filter] using ⟨hx, h_in⟩⟩
  have h_sum : ∑ U ∈ C, (f U).card = (C.biUnion f).card := by
    rw [Finset.card_biUnion h_disj]
  rw [h_sum, h_union]

/-- Global partition: Σ_{U ∈ C} Σ_{p ∈ P_Q} |pointFiber(p,U)| = Σ_{p ∈ P_Q} |T_Q p|.
    This is the key identity for the A2 H2 lower bound via pigeonhole. -/
lemma pointFiber_global_partition
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (C : Finset CoarseTube)
    (h_inj : Set.InjOn (parentCell Δ hΔ_pos) (C : Set CoarseTube))
    (h_cover : ∀ p ∈ P_Q, ∀ T_fine ∈ T_Q p, ∃ U ∈ C, InParent Δ hΔ_pos T_fine U) :
    ∑ U ∈ C, ∑ p ∈ P_Q, (pointFiber Δ hΔ_pos T_Q p U).card =
    ∑ p ∈ P_Q, (T_Q p).card := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact pointFiber_partition_single Δ hΔ_pos T_Q p C h_inj (h_cover p hp)

/-! ========================================================================
   Adapter 4: Canonical representative and cell-based partitions
   ======================================================================== -/

/-- All occupied parent cells across P_Q. -/
def allParentCells (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube) :
    Finset (DyadicTubeCell Δ) :=
  P_Q.biUnion (fun p => (T_Q p).image (parentCell Δ hΔ_pos))

/-- Existence of a fine tube in each occupied cell, with its point. -/
lemma existsTubeInCell_withPoint (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (cell : DyadicTubeCell Δ) (hcell : cell ∈ allParentCells Δ hΔ_pos P_Q T_Q) :
    ∃ (x : Plane × FineTube), x.1 ∈ P_Q ∧ x.2 ∈ T_Q x.1 ∧ parentCell Δ hΔ_pos x.2 = cell := by
  simp only [allParentCells, Finset.mem_biUnion] at hcell
  rcases hcell with ⟨p, hp, hmem⟩
  simp only [Finset.mem_image] at hmem
  rcases hmem with ⟨T, hT, rfl⟩
  exact ⟨(p, T), hp, hT, rfl⟩

/-- Existence of a fine tube in each occupied cell. -/
lemma existsTubeInCell (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (cell : DyadicTubeCell Δ) (hcell : cell ∈ allParentCells Δ hΔ_pos P_Q T_Q) :
    ∃ (T : FineTube), parentCell Δ hΔ_pos T = cell := by
  rcases existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell with ⟨x, _, _, h⟩
  exact ⟨x.2, h⟩

/-- Nonempty instance for FineTube (x-axis). -/
noncomputable instance fineTubeNonempty : Nonempty FineTube := by
  let p : EuclideanPlane := 0
  let v : EuclideanPlane := EuclideanSpace.single 0 1
  let ℓ : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' p (ℝ ∙ v)
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have h4 : v 0 = 0 := by rw [h] <;> simp
    have h5 : v 0 = 1 := by simp [v] <;> norm_num
    rw [h5] at h4 <;> norm_num at h4
  have h_finrank : Module.finrank ℝ ℓ.direction = 1 := by
    have h1 : ℓ.direction = ℝ ∙ v := by simp [ℓ]
    rw [h1, finrank_span_singleton hv_ne_zero] <;> norm_num
  exact ⟨⟨ℓ, h_finrank⟩⟩

/-- Canonical representative of a parent cell. Defined for all cells,
    but only correct when cell ∈ allParentCells. Guarantees the rep is in
    some T_Q p for p ∈ P_Q. -/
noncomputable def canonicalRepOfCell (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (cell : DyadicTubeCell Δ) : FineTube :=
  if hcell : cell ∈ allParentCells Δ hΔ_pos P_Q T_Q then
    (Classical.choose (existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell)).2
  else
    Classical.arbitrary FineTube

/-- The canonical rep has the correct parent cell (when cell is occupied). -/
lemma canonicalRepOfCell_correct (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (cell : DyadicTubeCell Δ) (hcell : cell ∈ allParentCells Δ hΔ_pos P_Q T_Q) :
    parentCell Δ hΔ_pos (canonicalRepOfCell Δ hΔ_pos P_Q T_Q cell) = cell := by
  dsimp only [canonicalRepOfCell]
  rw [dif_pos hcell]
  let x := Classical.choose (existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell)
  have h : x.1 ∈ P_Q ∧ x.2 ∈ T_Q x.1 ∧ parentCell Δ hΔ_pos x.2 = cell :=
    Classical.choose_spec (existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell)
  exact h.2.2

/-- The canonical rep belongs to P_Q.biUnion T_Q (when cell is occupied). -/
lemma canonicalRepOfCell_mem_biUnion (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (cell : DyadicTubeCell Δ) (hcell : cell ∈ allParentCells Δ hΔ_pos P_Q T_Q) :
    canonicalRepOfCell Δ hΔ_pos P_Q T_Q cell ∈ P_Q.biUnion T_Q := by
  dsimp only [canonicalRepOfCell]
  rw [dif_pos hcell]
  let x := Classical.choose (existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell)
  have h : x.1 ∈ P_Q ∧ x.2 ∈ T_Q x.1 ∧ parentCell Δ hΔ_pos x.2 = cell :=
    Classical.choose_spec (existsTubeInCell_withPoint Δ hΔ_pos P_Q T_Q cell hcell)
  exact Finset.mem_biUnion.mpr ⟨x.1, h.1, h.2.1⟩

/-- Cell-based single-point partition. -/
lemma pointFiber_perPoint_partition
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube) (p : Plane)
    (hp : p ∈ P_Q)
    (AllCells : Finset (DyadicTubeCell Δ))
    (hAllCells : AllCells = allParentCells Δ hΔ_pos P_Q T_Q) :
    ∑ cell ∈ AllCells, (pointFiber Δ hΔ_pos T_Q p
        (canonicalRepOfCell Δ hΔ_pos P_Q T_Q cell)).card = (T_Q p).card := by
  let rep := canonicalRepOfCell Δ hΔ_pos P_Q T_Q
  let C : Finset CoarseTube := AllCells.image rep
  have hcell_mem : ∀ cell ∈ AllCells, cell ∈ allParentCells Δ hΔ_pos P_Q T_Q := by
    intro cell hc
    rw [←hAllCells]
    exact hc
  have h_rep_inj : Set.InjOn rep (AllCells : Set (DyadicTubeCell Δ)) := by
    intro c1 hc1 c2 hc2 h_eq
    have h1 : parentCell Δ hΔ_pos (rep c1) = c1 :=
      canonicalRepOfCell_correct Δ hΔ_pos P_Q T_Q c1 (hcell_mem c1 hc1)
    have h2 : parentCell Δ hΔ_pos (rep c2) = c2 :=
      canonicalRepOfCell_correct Δ hΔ_pos P_Q T_Q c2 (hcell_mem c2 hc2)
    have h3 : parentCell Δ hΔ_pos (rep c1) = parentCell Δ hΔ_pos (rep c2) := by rw [h_eq]
    rw [h1, h2] at h3
    exact h3
  have h_inj : Set.InjOn (parentCell Δ hΔ_pos) (C : Set CoarseTube) := by
    intro U1 hU1 U2 hU2 h_eq
    rcases Finset.mem_image.mp hU1 with ⟨c1, hc1, rfl⟩
    rcases Finset.mem_image.mp hU2 with ⟨c2, hc2, rfl⟩
    have h1 : parentCell Δ hΔ_pos (rep c1) = c1 :=
      canonicalRepOfCell_correct Δ hΔ_pos P_Q T_Q c1 (hcell_mem c1 hc1)
    have h2 : parentCell Δ hΔ_pos (rep c2) = c2 :=
      canonicalRepOfCell_correct Δ hΔ_pos P_Q T_Q c2 (hcell_mem c2 hc2)
    have h3 : c1 = c2 := by
      rw [h1, h2] at h_eq
      exact h_eq
    rw [h3]
  have h_cover : ∀ T_fine ∈ T_Q p, ∃ U ∈ C, InParent Δ hΔ_pos T_fine U := by
    intro T_fine hT
    let cell := parentCell Δ hΔ_pos T_fine
    have hcell : cell ∈ AllCells := by
      rw [hAllCells, allParentCells, Finset.mem_biUnion]
      exact ⟨p, hp, Finset.mem_image.mpr ⟨T_fine, hT, rfl⟩⟩
    let U : CoarseTube := rep cell
    have hU : U ∈ C := Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    have h_in : InParent Δ hΔ_pos T_fine U := by
      dsimp only [InParent, U]
      rw [canonicalRepOfCell_correct Δ hΔ_pos P_Q T_Q cell (hcell_mem cell hcell)]
    exact ⟨U, hU, h_in⟩
  have h_main := pointFiber_partition_single Δ hΔ_pos T_Q p C h_inj h_cover
  have h_sum : ∑ cell ∈ AllCells, (pointFiber Δ hΔ_pos T_Q p (rep cell)).card =
      ∑ U ∈ C, (pointFiber Δ hΔ_pos T_Q p U).card := by
    have h : ∑ U ∈ C, (pointFiber Δ hΔ_pos T_Q p U).card =
        ∑ cell ∈ AllCells, (pointFiber Δ hΔ_pos T_Q p (rep cell)).card := by
      have h' : C = AllCells.image rep := by rfl
      rw [h']
      exact Finset.sum_image h_rep_inj
    exact h.symm
  rw [h_sum]
  exact h_main

/-- Cell-based global partition. -/
lemma pointFiber_total_partition
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube)
    (AllCells : Finset (DyadicTubeCell Δ))
    (hAllCells : AllCells = allParentCells Δ hΔ_pos P_Q T_Q) :
    ∑ cell ∈ AllCells, ∑ p ∈ P_Q,
      (pointFiber Δ hΔ_pos T_Q p (canonicalRepOfCell Δ hΔ_pos P_Q T_Q cell)).card =
    ∑ p ∈ P_Q, (T_Q p).card := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact pointFiber_perPoint_partition Δ hΔ_pos P_Q T_Q p hp AllCells hAllCells

/-! ========================================================================
   Adapter 5: Dyadic bin pigeonhole lemma
   ======================================================================== -/

/-- General dyadic bin pigeonhole: if items have weights ≤ 2^level,
    total weight ≥ S, and max level ≤ B,
    then ∃ j with 2^j * |{items at level j}| ≥ S/(B+1). -/
lemma dyadic_bin_pigeonhole
    {α : Type*} (s : Finset α) (w : α → ℝ) (level : α → ℕ)
    (hw_bound : ∀ x ∈ s, w x ≤ (2 : ℝ) ^ (level x))
    (S : ℝ) (hS : S ≤ ∑ x ∈ s, w x)
    (B : ℕ) (hB : ∀ x ∈ s, level x ≤ B) :
    ∃ j : ℕ, (2 : ℝ) ^ j * ((s.filter (fun x => level x = j)).card : ℝ) ≥ S / (B + 1 : ℝ) := by
  let bin (j : ℕ) : Finset α := s.filter (fun x => level x = j)
  have h_disj : ∀ j1 ∈ Finset.image level s, ∀ j2 ∈ Finset.image level s, j1 ≠ j2 → Disjoint (bin j1) (bin j2) := by
    intro j1 _ j2 _ hne
    simp only [bin, Finset.disjoint_left, Finset.mem_filter]
    intro x h1 h2
    have h3 : level x = j1 := h1.2
    have h4 : level x = j2 := h2.2
    rw [h3] at h4
    exact hne h4
  have h_union : (Finset.image level s).biUnion bin = s := by
    ext x
    simp only [Finset.mem_biUnion, bin, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hx, _⟩
      exact hx
    · intro hx
      refine ⟨level x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hx, rfl⟩
  have h_img : Finset.image level s ⊆ Finset.range (B + 1) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
    have h : level x ≤ B := hB x hx
    simp [Finset.mem_range] <;> omega
  have h_eq1 : ∑ x ∈ s, (2 : ℝ) ^ (level x) =
      ∑ j ∈ Finset.image level s, (2 : ℝ) ^ j * (bin j).card := by
    have h_step1 : ∑ x ∈ s, (2 : ℝ) ^ (level x) =
        ∑ j ∈ Finset.image level s, ∑ x ∈ bin j, (2 : ℝ) ^ (level x) := by
      rw [← Finset.sum_biUnion h_disj, h_union]
    rw [h_step1]
    apply Finset.sum_congr rfl
    intro j _
    have hlev : ∀ x ∈ bin j, level x = j := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hsum : ∑ x ∈ bin j, (2 : ℝ) ^ (level x) = ∑ x ∈ bin j, (2 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hlev x hx]
    rw [hsum]
    simp [mul_comm]
    <;> ring
  have h_eq2 : ∑ j ∈ Finset.image level s, (2 : ℝ) ^ j * (bin j).card =
      ∑ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card := by
    exact Finset.sum_subset h_img (fun j _ hj2 => by
      have h_empty : bin j = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x hx
        intro hlev
        have : j ∈ Finset.image level s := Finset.mem_image.mpr ⟨x, hx, hlev⟩
        exact hj2 this
      rw [h_empty]
      <;> simp)
  have h_le : ∑ x ∈ s, w x ≤ ∑ x ∈ s, (2 : ℝ) ^ (level x) := by
    gcongr with x hx
    exact hw_bound x hx
  have h1 : ∑ x ∈ s, w x ≤ ∑ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card := by
    calc ∑ x ∈ s, w x
      ≤ ∑ x ∈ s, (2 : ℝ) ^ (level x) := h_le
    _ = ∑ j ∈ Finset.image level s, (2 : ℝ) ^ j * (bin j).card := h_eq1
    _ = ∑ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card := h_eq2
  have h2 : S ≤ ∑ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card :=
    le_trans hS h1
  by_cases hS' : S ≤ 0
  · refine ⟨0, ?_⟩
    have h_S_nonpos : S / (B + 1 : ℝ) ≤ 0 := by
      have hB_pos : (0 : ℝ) < (B + 1 : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg hS' (by positivity)
    have h_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (0 : ℕ) * (bin 0).card := by positivity
    exact le_trans h_S_nonpos h_nonneg
  · have hS_pos : 0 < S := by linarith
    by_contra h
    push Not at h
    have h_le_all : ∀ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card ≤ S / (B + 1 : ℝ) := by
      intro j hj
      have h5 : (2 : ℝ) ^ j * ((s.filter (fun x => level x = j)).card : ℝ) < S / (B + 1 : ℝ) := h j
      have h6 : (s.filter (fun x => level x = j)) = bin j := by rfl
      rw [h6] at h5
      exact h5.le
    have h_strict : ∃ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card < S / (B + 1 : ℝ) := by
      have h5 : (2 : ℝ) ^ (0 : ℕ) * ((s.filter (fun x => level x = 0)).card : ℝ) < S / (B + 1 : ℝ) := h 0
      have h6 : (s.filter (fun x => level x = 0)) = bin 0 := by rfl
      rw [h6] at h5
      exact ⟨0, by simp, h5⟩
    have h3 : ∑ j ∈ Finset.range (B + 1), (2 : ℝ) ^ j * (bin j).card <
        ∑ j ∈ Finset.range (B + 1), S / (B + 1 : ℝ) :=
      Finset.sum_lt_sum h_le_all h_strict
    have h4 : ∑ j ∈ Finset.range (B + 1), S / (B + 1 : ℝ) = S := by
      simp [Finset.sum_const, Finset.card_range]
      <;> field_simp <;> ring
    rw [h4] at h3
    exact False.elim (not_le.mpr h3 h2)

/-! ========================================================================
   Adapter 6: Parent cell geometric containment
   ======================================================================== -/

/-- If two tubes' parent cell indices differ by at most r in each coordinate,
    then their line distance ≤ 10*(r+1)*Δ. -/
lemma parentCell_ball_containment
    (Δ : ℝ) (hΔ_pos : 0 < Δ) (r : ℝ) (hr_nonneg : 0 ≤ r)
    (T U : FineTube)
    (hcell1 : |(parentCell Δ hΔ_pos T).1 - (parentCell Δ hΔ_pos U).1| ≤ r)
    (hcell2 : |(parentCell Δ hΔ_pos T).2 - (parentCell Δ hΔ_pos U).2| ≤ r)
    (hvT : (getDirV T) 1 ≠ 0) (hvU : (getDirV U) 1 ≠ 0)
    (haT : |tubeSlope T| ≤ 1) (haU : |tubeSlope U| ≤ 1)
    (hbT : |tubeIntercept T| ≤ 3) (hbU : |tubeIntercept U| ≤ 3) :
    dist T U ≤ 10 * (r + 1) * Δ := by
  let aT := tubeSlope T
  let bT := tubeIntercept T
  let aU := tubeSlope U
  let bU := tubeIntercept U
  let kT1 := (parentCell Δ hΔ_pos T).1
  let kU1 := (parentCell Δ hΔ_pos U).1
  let kT2 := (parentCell Δ hΔ_pos T).2
  let kU2 := (parentCell Δ hΔ_pos U).2
  have hΔ_ne : Δ ≠ 0 := hΔ_pos.ne'
  have hpos : 0 ≤ Δ := hΔ_pos.le
  have hcell1' : |(kT1 : ℝ) - (kU1 : ℝ)| ≤ r := by exact_mod_cast hcell1
  have hcell2' : |(kT2 : ℝ) - (kU2 : ℝ)| ≤ r := by exact_mod_cast hcell2
  have ha1 : |aT - aU| ≤ (r + 1) * Δ := by
    have h11 : (kT1 : ℝ) ≤ aT / Δ := Int.floor_le _
    have h12 : aT / Δ < (kT1 : ℝ) + 1 := Int.lt_floor_add_one _
    have h21 : (kU1 : ℝ) ≤ aU / Δ := Int.floor_le _
    have h22 : aU / Δ < (kU1 : ℝ) + 1 := Int.lt_floor_add_one _
    have h_abs : |(kT1 : ℝ) - (kU1 : ℝ)| ≤ r := hcell1'
    have h_diff1 : aT / Δ - aU / Δ < r + 1 := by
      have h : (kT1 : ℝ) - (kU1 : ℝ) ≤ r := by
        have h' := abs_le.mp h_abs
        linarith
      linarith
    have h_diff2 : aU / Δ - aT / Δ < r + 1 := by
      have h : (kU1 : ℝ) - (kT1 : ℝ) ≤ r := by
        have h' := abs_le.mp h_abs
        linarith
      linarith
    have h3 : |aT / Δ - aU / Δ| < r + 1 := by
      rw [abs_lt] <;> constructor <;> linarith
    have h5 : |aT - aU| = Δ * |aT / Δ - aU / Δ| := by
      have h6 : aT - aU = Δ * (aT / Δ - aU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h6, abs_mul, abs_of_pos hΔ_pos]
    rw [h5]
    have h7 : Δ * |aT / Δ - aU / Δ| ≤ Δ * (r + 1) := by gcongr <;> linarith
    linarith
  have hb1 : |bT - bU| ≤ (r + 1) * Δ := by
    have h11 : (kT2 : ℝ) ≤ bT / Δ := Int.floor_le _
    have h12 : bT / Δ < (kT2 : ℝ) + 1 := Int.lt_floor_add_one _
    have h21 : (kU2 : ℝ) ≤ bU / Δ := Int.floor_le _
    have h22 : bU / Δ < (kU2 : ℝ) + 1 := Int.lt_floor_add_one _
    have h_abs : |(kT2 : ℝ) - (kU2 : ℝ)| ≤ r := hcell2'
    have h_diff1 : bT / Δ - bU / Δ < r + 1 := by
      have h : (kT2 : ℝ) - (kU2 : ℝ) ≤ r := by
        have h' := abs_le.mp h_abs
        linarith
      linarith
    have h_diff2 : bU / Δ - bT / Δ < r + 1 := by
      have h : (kU2 : ℝ) - (kT2 : ℝ) ≤ r := by
        have h' := abs_le.mp h_abs
        linarith
      linarith
    have h3 : |bT / Δ - bU / Δ| < r + 1 := by
      rw [abs_lt] <;> constructor <;> linarith
    have h5 : |bT - bU| = Δ * |bT / Δ - bU / Δ| := by
      have h6 : bT - bU = Δ * (bT / Δ - bU / Δ) := by field_simp [hΔ_ne] <;> ring
      rw [h6, abs_mul, abs_of_pos hΔ_pos]
    rw [h5]
    have h7 : Δ * |bT / Δ - bU / Δ| ≤ Δ * (r + 1) := by gcongr <;> linarith
    linarith
  have h_param : dist (aT, bT) (aU, bU) ≤ (r + 1) * Δ := by
    have h_main : dist (aT, bT) (aU, bU) = max (|aT - aU|) (|bT - bU|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h_main]
    exact max_le ha1 hb1
  have h_antilipschitz : dist T U ≤ 10 * dist (aT, bT) (aU, bU) :=
    affineLineParams_antilipschitz T U hvT hvU haT haU hbT hbU
  calc dist T U
    ≤ 10 * dist (aT, bT) (aU, bU) := h_antilipschitz
  _ ≤ 10 * ((r + 1) * Δ) := by gcongr
  _ = 10 * (r + 1) * Δ := by ring

end DirecretisedFurstenbergEstimate.AppendixA.H2Migration
