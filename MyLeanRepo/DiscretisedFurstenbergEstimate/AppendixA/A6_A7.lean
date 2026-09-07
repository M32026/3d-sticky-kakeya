module

/-
  Helper definitions for A5 C_pi/fiber double counting and energy utilities.

  Originally contained A6 quantitative bounds and A7 extraction, but those
  were removed in favor of the geometric energy route in DirectGeometricEnergy.

  Retained helpers:
  - a5Cpi, a5Fiber: total C_Q_pi and fiber lookup
  - a5_double_counting: Σ_Q |a5Cpi Q| = Σ_T |a5Fiber T|
  - coarseSquare_dist_one, coarseSquare_separated, ncover_coarse_eq_card
  - rpow_add_eq, rpow_sub_eq
  - pointEnergy_nonneg, pairEnergy_nonneg, pointEnergy_le_pairEnergy
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Phase2

/-! ========================================================================
   Total helper functions for A5 C_pi and fiber
   ======================================================================== -/

/-- Total version of C_Q_pi lookup: returns empty set if Q not in Qset. -/
def a5Cpi {Δ δ s t ε : ℝ} (a5 : A5_Output Δ δ s t ε)
    (Q : CoarseSquare Δ) : Finset CoarseTube :=
  if h : Q ∈ a5.Qset then (a5.perSquare Q h).C_Q_pi ∩ a5.C_global else ∅

lemma a5Cpi_eq {Δ δ s t ε : ℝ} (a5 : A5_Output Δ δ s t ε)
    {Q : CoarseSquare Δ} (hQ : Q ∈ a5.Qset) :
    a5Cpi a5 Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by
  simp [a5Cpi, hQ]

/-- Fiber of coarse squares Q for which T ∈ C_Q_pi. -/
def a5Fiber {Δ δ s t ε : ℝ} (a5 : A5_Output Δ δ s t ε)
    (T : CoarseTube) : Finset (CoarseSquare Δ) :=
  a5.Qset.filter (fun Q => T ∈ a5Cpi a5 Q)

lemma a5Fiber_subset {Δ δ s t ε : ℝ} (a5 : A5_Output Δ δ s t ε)
    {T : CoarseTube} : a5Fiber a5 T ⊆ a5.Qset :=
  Finset.filter_subset _ _

/-! ========================================================================
   Helper: CoarseSquare separation and covering number
   ======================================================================== -/

lemma coarseSquare_dist_one {Δ : ℝ} {q1 q2 : CoarseSquare Δ} (h : q1 ≠ q2) :
    1 ≤ dist q1 q2 := by
  have h4 : q1.1 ≠ q2.1 ∨ q1.2 ≠ q2.2 := by
    by_contra h5
    push Not at h5
    exact h (Prod.ext h5.1 h5.2)
  rcases h4 with (h4 | h4)
  · have h5 : (1 : ℝ) ≤ |(q1.1 : ℝ) - (q2.1 : ℝ)| := by
      have h6 : q1.1 - q2.1 ≠ 0 := by omega
      have h7 : 1 ≤ |q1.1 - q2.1| := by exact Int.one_le_abs h6
      exact_mod_cast h7
    have h8 : dist q1 q2 = max |(q1.1 : ℝ) - (q2.1 : ℝ)| |(q1.2 : ℝ) - (q2.2 : ℝ)| := by rfl
    rw [h8]; exact le_max_of_le_left h5
  · have h5 : (1 : ℝ) ≤ |(q1.2 : ℝ) - (q2.2 : ℝ)| := by
      have h6 : q1.2 - q2.2 ≠ 0 := by omega
      have h7 : 1 ≤ |q1.2 - q2.2| := by exact Int.one_le_abs h6
      exact_mod_cast h7
    have h8 : dist q1 q2 = max |(q1.1 : ℝ) - (q2.1 : ℝ)| |(q1.2 : ℝ) - (q2.2 : ℝ)| := by rfl
    rw [h8]; exact le_max_of_le_right h5

lemma coarseSquare_separated {Δ : ℝ} (hΔ_lt_one : Δ < 1) {Q : Finset (CoarseSquare Δ)} :
    SeparatedAt Δ (Q : Set (CoarseSquare Δ)) := by
  intro q1 _ q2 _ hne
  have h1 : (1 : ℝ) ≤ dist q1 q2 := coarseSquare_dist_one hne
  have h2 : Δ ≤ (1 : ℝ) := by linarith
  linarith

lemma ncover_coarse_eq_card {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    {Q : Finset (CoarseSquare Δ)} :
    ENNReal.ofReal (Q.card : ℝ) = Phase2.Ncover Δ (Q : Set (CoarseSquare Δ)) := by
  have h_sep : SeparatedAt Δ (Q : Set (CoarseSquare Δ)) :=
    coarseSquare_separated (by linarith)
  have h_pack : ∀ (x : CoarseSquare Δ),
      (Q.filter (fun y => dist y x ≤ Δ)).card ≤ 1 := by
    intro x
    by_contra h
    have h2 : 1 < (Q.filter (fun y => dist y x ≤ Δ)).card := by omega
    rcases Finset.one_lt_card.mp h2 with ⟨y, hy, z, hz, hyz⟩
    have hdy : dist y x ≤ Δ := (Finset.mem_filter.mp hy).2
    have hdz : dist z x ≤ Δ := (Finset.mem_filter.mp hz).2
    have h3 : dist y z ≤ 2 * Δ := by
      calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
           _ ≤ Δ + Δ := by linarith [dist_comm x z]
           _ = 2 * Δ := by ring
    have h4 : (1 : ℝ) ≤ dist y z := coarseSquare_dist_one hyz
    linarith
  have h_lower1 : (Q.card : ENNReal) ≤ Metric.externalCoveringNumber Δ.toNNReal (Q : Set (CoarseSquare Δ)) := by
    have h := SSetBridges.packing_cover_generic hΔ_pos h_sep (hK_pos := by norm_num) h_pack
    simpa using h
  have h_lower : (Q.card : ENNReal) ≤ Phase2.Ncover Δ (Q : Set (CoarseSquare Δ)) := by
    simpa [Phase2.Ncover] using h_lower1
  have h_upper : Phase2.Ncover Δ (Q : Set (CoarseSquare Δ)) ≤ (Q.card : ENNReal) :=
    ncover_le_card hΔ_pos
  have h_eq1 : ENNReal.ofReal (Q.card : ℝ) = (Q.card : ENNReal) := by simp
  rw [h_eq1]
  exact le_antisymm h_lower h_upper

/-! ========================================================================
   rpow helpers
   ======================================================================== -/

lemma rpow_add_eq {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    Real.rpow x (y + z) = Real.rpow x y * Real.rpow x z :=
  Real.rpow_add hx y z

lemma rpow_sub_eq {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    Real.rpow x (y - z) = Real.rpow x y / Real.rpow x z := by
  have h_pos : 0 < Real.rpow x z := Real.rpow_pos_of_pos hx z
  have h_eq : Real.rpow x (y - z) * Real.rpow x z = Real.rpow x y := by
    have h3 := Real.rpow_add hx (y - z) z
    have h4 : (y - z) + z = y := by ring
    rw [h4] at h3
    exact h3.symm
  calc
    Real.rpow x (y - z)
      = (Real.rpow x (y - z) * Real.rpow x z) / Real.rpow x z := by
        field_simp [h_pos.ne'] <;> ring
  _ = Real.rpow x y / Real.rpow x z := by rw [h_eq]

/-! ========================================================================
   Double counting identity
   ======================================================================== -/

lemma a5_double_counting {Δ δ s t ε : ℝ} (a5 : A5_Output Δ δ s t ε) :
    ∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card =
    ∑ T ∈ a5.C_global, (a5Fiber a5 T).card := by
  have h_sub : ∀ Q ∈ a5.Qset, a5Cpi a5 Q ⊆ a5.C_global := by
    intro Q hQ
    rw [a5Cpi_eq a5 hQ]
    have h : (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global ⊆ a5.C_global := by
      simp
    exact h
  have h1 : ∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card =
      ∑ Q ∈ a5.Qset, ∑ T ∈ a5.C_global, if T ∈ a5Cpi a5 Q then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro Q hQ
    have h4 : ∑ T ∈ a5.C_global, (if T ∈ a5Cpi a5 Q then 1 else 0) =
        (a5Cpi a5 Q).card := by
      rw [Finset.sum_ite]
      <;> simp [h_sub Q hQ, Finset.filter_true_of_mem]
      <;> rfl
    exact h4.symm
  rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  have h5 : ∑ Q ∈ a5.Qset, (if T ∈ a5Cpi a5 Q then 1 else 0) =
      (a5Fiber a5 T).card := by
    have h6 : ∑ Q ∈ a5.Qset, (if T ∈ a5Cpi a5 Q then 1 else 0) =
        ∑ Q ∈ (a5.Qset.filter (fun Q => T ∈ a5Cpi a5 Q)), 1 := by
      rw [Finset.sum_filter]
      <;> simp
    rw [h6]
    <;> simp [a5Fiber]
    <;> rfl
  exact h5

/-! ========================================================================
   pointEnergy / pairEnergy nonnegativity
   ======================================================================== -/

lemma pointEnergy_nonneg {X : Type*} [MetricSpace X] [DecidableEq X]
    {u : ℝ} {P : Finset X} {x : X} : 0 ≤ pointEnergy u P x := by
  dsimp only [pointEnergy]
  apply Finset.sum_nonneg
  intro y _
  exact Real.rpow_nonneg dist_nonneg _

lemma pairEnergy_nonneg {X : Type*} [MetricSpace X] [DecidableEq X]
    {u : ℝ} {P : Finset X} : 0 ≤ pairEnergy u P := by
  dsimp only [pairEnergy]
  apply Finset.sum_nonneg
  intro x _
  exact pointEnergy_nonneg

lemma pointEnergy_le_pairEnergy {X : Type*} [MetricSpace X] [DecidableEq X]
    {u : ℝ} {P : Finset X} {x : X} (hx : x ∈ P) :
    pointEnergy u P x ≤ pairEnergy u P := by
  dsimp only [pairEnergy]
  apply Finset.single_le_sum (fun z _ => pointEnergy_nonneg) hx

end DirecretisedFurstenbergEstimate.AppendixA
