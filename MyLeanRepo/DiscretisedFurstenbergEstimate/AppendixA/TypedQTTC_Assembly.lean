module

/-
  Typed QTTC assembly for dyadic tube families using sourceParent.

  Uses centerRep (center of coarse parent cell) as the QTTC coarsening map:
    coarse T = centerRep (sourceParent T)

  This ensures assignedCount coarse = pointFiber (exact source-parent fibers),
  while satisfying QTTC's distance and separation requirements at Δ = dyadicDelta m.

  Whiteprint node: appendix_a_alternative / typed_qttc_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.InductionOnScales
open DirecretisedFurstenbergEstimate.AppendixA

-- Alias to avoid ambiguity
abbrev sp {n m : ℕ} (hnm : m ≤ n) := TypedDyadicInfrastructure.sourceParent hnm

-- Explicit aliases to avoid shadowing by Interfaces.lean
abbrev qttcAssignedCount {α L : Type*} [DecidableEq L]
    (coarse : L → L) (T : α → Finset L) (p : α) (c : L) : ℕ :=
  ((T p).filter fun ℓ => coarse ℓ = c).card

/-- Generalized pointFiber for arbitrary point type α. -/
abbrev pointFiberG {α : Type*} {n m : ℕ} (hnm : m ≤ n)
    (tubeFamily : α → Finset (DyadicTube n))
    (p : α) (U : DyadicTube m) : Finset (DyadicTube n) :=
  (tubeFamily p).filter (fun T => sp hnm T = U)

/-- Generalized global coarse family for arbitrary point type α. -/
abbrev globalCoarseG {α : Type*} [DecidableEq α] {n m : ℕ} (hnm : m ≤ n)
    (P : Finset α) (tubeFamily : α → Finset (DyadicTube n)) :
    Finset (DyadicTube m) :=
  Finset.image (sp hnm) (P.biUnion tubeFamily)

/-! ========================================================================
   1. centerRep: center of coarse parent cell, lifted to fine scale
   ======================================================================== -/

/-- Center representative of a coarse dyadic tube parent cell. -/
def centerRep {n m : ℕ} (hnm : m ≤ n) (U : DyadicTube m) : DyadicTube n :=
  let R : ℤ := refinementFactor n m
  ⟨U.a * R + R / 2, U.b * R + R / 2⟩

/-- centerRep is injective. -/
lemma centerRep_injective {n m : ℕ} (hnm : m ≤ n) :
    Function.Injective (centerRep hnm) := by
  intro U1 U2 h
  let R : ℤ := refinementFactor n m
  have hR_nat : 0 < refinementFactor n m := refinementFactor_pos n m
  have hR_pos : (0 : ℤ) < R := by
    dsimp only [R]
    exact_mod_cast hR_nat
  have ha : (centerRep hnm U1).a = (centerRep hnm U2).a := by rw [h]
  have hb : (centerRep hnm U1).b = (centerRep hnm U2).b := by rw [h]
  have ha' : U1.a * R + R / 2 = U2.a * R + R / 2 := by
    have h2 : (centerRep hnm U1).a = U1.a * R + R / 2 := by rfl
    have h3 : (centerRep hnm U2).a = U2.a * R + R / 2 := by rfl
    rw [h2, h3] at ha
    exact ha
  have hb' : U1.b * R + R / 2 = U2.b * R + R / 2 := by
    have h2 : (centerRep hnm U1).b = U1.b * R + R / 2 := by rfl
    have h3 : (centerRep hnm U2).b = U2.b * R + R / 2 := by rfl
    rw [h2, h3] at hb
    exact hb
  have ha_eq : U1.a = U2.a := by
    have h : U1.a * R = U2.a * R := by linarith
    have h' : (U1.a - U2.a) * R = 0 := by linarith
    have h'' : U1.a - U2.a = 0 := by
      apply (mul_eq_zero.mp h').resolve_right
      exact hR_pos.ne'
    linarith
  have hb_eq : U1.b = U2.b := by
    have h : U1.b * R = U2.b * R := by linarith
    have h' : (U1.b - U2.b) * R = 0 := by linarith
    have h'' : U1.b - U2.b = 0 := by
      apply (mul_eq_zero.mp h').resolve_right
      exact hR_pos.ne'
    linarith
  cases U1; cases U2; simp_all

/-- Distance preservation: centerRep is an isometric embedding. -/
lemma centerRep_dist_eq {n m : ℕ} (hnm : m ≤ n) (U1 U2 : DyadicTube m) :
    (centerRep hnm U1).dist (centerRep hnm U2) = U1.dist U2 := by
  let R : ℕ := refinementFactor n m
  have hR_nat : 0 < R := refinementFactor_pos n m
  have hR_pos_int : (0 : ℤ) < (R : ℤ) := by exact_mod_cast hR_nat
  have h_scale : dyadicDelta n * (R : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  have h_a_diff : (centerRep hnm U1).a - (centerRep hnm U2).a =
      (U1.a - U2.a) * (R : ℤ) := by
    simp [centerRep] <;> ring
  have h_b_diff : (centerRep hnm U1).b - (centerRep hnm U2).b =
      (U1.b - U2.b) * (R : ℤ) := by
    simp [centerRep] <;> ring
  have h1 : (|((centerRep hnm U1).a - (centerRep hnm U2).a : ℤ)| : ℝ) =
      (R : ℝ) * (|(U1.a - U2.a : ℤ)| : ℝ) := by
    have h1a : |((centerRep hnm U1).a - (centerRep hnm U2).a : ℤ)| =
        (R : ℤ) * |(U1.a - U2.a : ℤ)| := by
      rw [h_a_diff, abs_mul, abs_of_pos hR_pos_int] <;> ring
    exact_mod_cast h1a
  have h2 : (|((centerRep hnm U1).b - (centerRep hnm U2).b : ℤ)| : ℝ) =
      (R : ℝ) * (|(U1.b - U2.b : ℤ)| : ℝ) := by
    have h2a : |((centerRep hnm U1).b - (centerRep hnm U2).b : ℤ)| =
        (R : ℤ) * |(U1.b - U2.b : ℤ)| := by
      rw [h_b_diff, abs_mul, abs_of_pos hR_pos_int] <;> ring
    exact_mod_cast h2a
  have h_goal : dyadicDelta n *
      ((|((centerRep hnm U1).a - (centerRep hnm U2).a : ℤ)| : ℝ) +
       (|((centerRep hnm U1).b - (centerRep hnm U2).b : ℤ)| : ℝ)) =
      dyadicDelta m *
      ((|(U1.a - U2.a : ℤ)| : ℝ) + (|(U1.b - U2.b : ℤ)| : ℝ)) := by
    have h_factor : dyadicDelta n * ((R : ℝ) * (|(U1.a - U2.a : ℤ)| : ℝ) + (R : ℝ) * (|(U1.b - U2.b : ℤ)| : ℝ)) =
        dyadicDelta n * (R : ℝ) * ((|(U1.a - U2.a : ℤ)| : ℝ) + (|(U1.b - U2.b : ℤ)| : ℝ)) := by ring
    rw [h1, h2, h_factor, h_scale] <;> ring
  simpa [DyadicTube.dist_eq] using h_goal

/-- sourceParent of centerRep gives back the original parent. -/
lemma sourceParent_centerRep {n m : ℕ} (hnm : m ≤ n) (U : DyadicTube m) :
    sp hnm (centerRep hnm U) = U := by
  let R : ℤ := refinementFactor n m
  have hR_nat : 0 < refinementFactor n m := refinementFactor_pos n m
  have hR_pos : (0 : ℤ) < R := by
    dsimp only [R]
    exact_mod_cast hR_nat
  have h_cr1 : 0 ≤ R / 2 := by omega
  have h_cr2 : R / 2 < R := by omega
  have h_div_a : (U.a * R + R / 2) / R = U.a := by
    have h_comm : U.a * R + R / 2 = R / 2 + R * U.a := by ring
    rw [h_comm]
    have h : (R / 2 + R * U.a) / R = (R / 2) / R + U.a := by
      exact Int.add_mul_ediv_left (R / 2) U.a hR_pos.ne'
    rw [h]
    have h_zero : (R / 2) / R = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    rw [h_zero] <;> omega
  have h_div_b : (U.b * R + R / 2) / R = U.b := by
    have h_comm : U.b * R + R / 2 = R / 2 + R * U.b := by ring
    rw [h_comm]
    have h : (R / 2 + R * U.b) / R = (R / 2) / R + U.b := by
      exact Int.add_mul_ediv_left (R / 2) U.b hR_pos.ne'
    rw [h]
    have h_zero : (R / 2) / R = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    rw [h_zero] <;> omega
  have h_goal : sp hnm (centerRep hnm U) =
      (⟨(U.a * R + R / 2) / R, (U.b * R + R / 2) / R⟩ : DyadicTube m) := by
    rfl
  rw [h_goal, h_div_a, h_div_b]
  <;> rfl

/-- Distance from any fine tube T to the center representative of its
    source parent is at most dyadicDelta m. -/
lemma centerRep_dist_bound {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    T.dist (centerRep hnm (sp hnm T)) ≤ dyadicDelta m := by
  let U := sp hnm T
  let R : ℕ := refinementFactor n m
  have hR_nat : 0 < R := refinementFactor_pos n m
  have hR_pos_int : (0 : ℤ) < (R : ℤ) := by exact_mod_cast hR_nat
  have h_scale : dyadicDelta n * (R : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  let cR : ℤ := (R : ℤ) / 2
  have h_cr1 : 0 ≤ cR := by omega
  have h_cr2 : cR < (R : ℤ) := by omega
  have h_contain : U.a * (R : ℤ) ≤ T.a ∧ T.a < (U.a + 1) * (R : ℤ) ∧
      U.b * (R : ℤ) ≤ T.b ∧ T.b < (U.b + 1) * (R : ℤ) :=
    (TypedDyadicInfrastructure.sourceParent_containment hnm T U).mp rfl
  set x : ℤ := T.a - U.a * (R : ℤ) with hx_def
  set y : ℤ := T.b - U.b * (R : ℤ) with hy_def
  have hx1 : 0 ≤ x := by linarith [h_contain.1]
  have hx2 : x < (R : ℤ) := by linarith [h_contain.2.1]
  have hy1 : 0 ≤ y := by linarith [h_contain.2.2.1]
  have hy2 : y < (R : ℤ) := by linarith [h_contain.2.2.2]
  have h_rabs : |x - cR| ≤ cR := by
    rw [abs_le]
    constructor <;> omega
  have h_rbs : |y - cR| ≤ cR := by
    rw [abs_le]
    constructor <;> omega
  have h_ca : (centerRep hnm U).a = U.a * (R : ℤ) + cR := by rfl
  have h_cb : (centerRep hnm U).b = U.b * (R : ℤ) + cR := by rfl
  have h1 : |(T.a - (centerRep hnm U).a : ℤ)| ≤ cR := by
    have h_eq : T.a - (centerRep hnm U).a = x - cR := by
      simp [h_ca, hx_def] <;> ring
    rw [h_eq]
    exact h_rabs
  have h2 : |(T.b - (centerRep hnm U).b : ℤ)| ≤ cR := by
    have h_eq : T.b - (centerRep hnm U).b = y - cR := by
      simp [h_cb, hy_def] <;> ring
    rw [h_eq]
    exact h_rbs
  have h3 : (cR : ℝ) + (cR : ℝ) ≤ (R : ℝ) := by
    have h4 : cR + cR ≤ (R : ℤ) := by omega
    exact_mod_cast h4
  have h_sum : (|(T.a - (centerRep hnm U).a : ℤ)| : ℝ) +
      (|(T.b - (centerRep hnm U).b : ℤ)| : ℝ) ≤ (R : ℝ) := by
    have h5 : (|(T.a - (centerRep hnm U).a : ℤ)| : ℝ) ≤ (cR : ℝ) := by exact_mod_cast h1
    have h6 : (|(T.b - (centerRep hnm U).b : ℤ)| : ℝ) ≤ (cR : ℝ) := by exact_mod_cast h2
    linarith
  have h5 : dyadicDelta n * ((|(T.a - (centerRep hnm U).a : ℤ)| : ℝ) +
      (|(T.b - (centerRep hnm U).b : ℤ)| : ℝ)) ≤ dyadicDelta n * (R : ℝ) := by
    exact mul_le_mul_of_nonneg_left h_sum hδn_pos.le
  have h6 : dyadicDelta n * (R : ℝ) = dyadicDelta m := h_scale
  have h7 : T.dist (centerRep hnm U) =
      dyadicDelta n * ((|(T.a - (centerRep hnm U).a : ℤ)| : ℝ) +
        (|(T.b - (centerRep hnm U).b : ℤ)| : ℝ)) := by
    rw [DyadicTube.dist_eq]
  rw [h7]
  linarith [h5, h6]

/-- The image of any set of coarse parents under centerRep is
    dyadicDelta m-separated. -/
lemma centerRep_separated {n m : ℕ} (hnm : m ≤ n)
    (S : Finset (DyadicTube m)) :
    SeparatedAt (dyadicDelta m) (Finset.image (centerRep hnm) S : Set (DyadicTube n)) := by
  intro x hx y hy hne
  rcases Finset.mem_image.mp hx with ⟨U1, hU1, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨U2, hU2, rfl⟩
  have hU_ne : U1 ≠ U2 := by
    intro h; rw [h] at hne; exact hne rfl
  have h_dist : (centerRep hnm U1).dist (centerRep hnm U2) = U1.dist U2 :=
    centerRep_dist_eq hnm U1 U2
  have h_or : U1.a ≠ U2.a ∨ U1.b ≠ U2.b := by
    by_contra h
    push Not at h
    have h_eq : U1 = U2 := by
      cases U1; cases U2; simp_all
    exact hU_ne h_eq
  have h_sum : (|(U1.a - U2.a : ℤ)| : ℝ) + (|(U1.b - U2.b : ℤ)| : ℝ) ≥ 1 := by
    rcases h_or with (h_or | h_or)
    · have h_ne : U1.a - U2.a ≠ 0 := by omega
      have h4 : |(U1.a - U2.a : ℤ)| ≥ 1 := Int.one_le_abs h_ne
      have h5 : (|(U1.a - U2.a : ℤ)| : ℝ) ≥ 1 := by exact_mod_cast h4
      have h6 : (|(U1.b - U2.b : ℤ)| : ℝ) ≥ 0 := by positivity
      linarith
    · have h_ne : U1.b - U2.b ≠ 0 := by omega
      have h4 : |(U1.b - U2.b : ℤ)| ≥ 1 := Int.one_le_abs h_ne
      have h5 : (|(U1.b - U2.b : ℤ)| : ℝ) ≥ 1 := by exact_mod_cast h4
      have h6 : (|(U1.a - U2.a : ℤ)| : ℝ) ≥ 0 := by positivity
      linarith
  have h_ge : U1.dist U2 ≥ dyadicDelta m := by
    rw [DyadicTube.dist_eq]
    have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
    have h7 : dyadicDelta m * ((|(U1.a - U2.a : ℤ)| : ℝ) + (|(U1.b - U2.b : ℤ)| : ℝ)) ≥ dyadicDelta m := by
      calc dyadicDelta m * ((|(U1.a - U2.a : ℤ)| : ℝ) + (|(U1.b - U2.b : ℤ)| : ℝ))
        ≥ dyadicDelta m * 1 := by gcongr
      _ = dyadicDelta m := by ring
    exact h7
  have h_ge2 : (centerRep hnm U1).dist (centerRep hnm U2) ≥ dyadicDelta m := by
    rw [h_dist] <;> exact h_ge
  have h_final : dyadicDelta m ≤ dist (centerRep hnm U1) (centerRep hnm U2) := by
    have h_dist3 : dist (centerRep hnm U1) (centerRep hnm U2) = (centerRep hnm U1).dist (centerRep hnm U2) := by
      rfl
    rw [h_dist3]
    exact h_ge2
  exact h_final

/-! ========================================================================
   2. Cardinality bound for bounded dyadic tube families
   ======================================================================== -/

/-- Cardinality bound for bounded dyadic tubes. -/
lemma dyadicTubes_bounded_card {m : ℕ} (hm_pos : 1 ≤ m)
    (S : Finset (DyadicTube m))
    (h_slope : ∀ U ∈ S, |U.slope| ≤ 1)
    (h_intercept : ∀ U ∈ S, |U.intercept| ≤ 3) :
    (S.card : ℝ) ≤ 100 * (dyadicDelta m) ^ (-2 : ℝ) := by
  have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  let N : ℕ := 2 ^ m
  have hN_pos : 0 < N := by positivity
  have hδ_eq : dyadicDelta m = 1 / (N : ℝ) := by
    simp [dyadicDelta, N] <;> norm_cast
  have ha_bound : ∀ U ∈ S, |(U.a : ℝ)| ≤ (N : ℝ) := by
    intro U hU
    have h : |U.slope| ≤ 1 := h_slope U hU
    have h2 : U.slope = (U.a : ℝ) * dyadicDelta m := by rfl
    rw [h2] at h
    have h3 : |(U.a : ℝ)| * dyadicDelta m ≤ 1 := by
      have h4 : |(U.a : ℝ) * dyadicDelta m| ≤ 1 := h
      have h5 : |(U.a : ℝ) * dyadicDelta m| = |(U.a : ℝ)| * dyadicDelta m := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h5] at h4
      exact h4
    rw [hδ_eq] at h3
    have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    have h7 : |(U.a : ℝ)| * (1 / (N : ℝ)) * (N : ℝ) ≤ 1 * (N : ℝ) := by gcongr
    have h10 : (1 / (N : ℝ)) * (N : ℝ) = 1 := by
      field_simp [hN_pos'.ne']
    have h9 : |(U.a : ℝ)| * (1 / (N : ℝ)) * (N : ℝ) = |(U.a : ℝ)| := by
      rw [mul_assoc, h10]
      <;> ring
    rw [h9] at h7
    linarith
  have hb_bound : ∀ U ∈ S, |(U.b : ℝ)| ≤ (3 * N : ℝ) := by
    intro U hU
    have h : |U.intercept| ≤ 3 := h_intercept U hU
    have h2 : U.intercept = (U.b : ℝ) * dyadicDelta m := by rfl
    rw [h2] at h
    have h3 : |(U.b : ℝ)| * dyadicDelta m ≤ 3 := by
      have h4 : |(U.b : ℝ) * dyadicDelta m| ≤ 3 := h
      have h5 : |(U.b : ℝ) * dyadicDelta m| = |(U.b : ℝ)| * dyadicDelta m := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h5] at h4
      exact h4
    rw [hδ_eq] at h3
    have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    have h7 : |(U.b : ℝ)| * (1 / (N : ℝ)) * (N : ℝ) ≤ 3 * (N : ℝ) := by gcongr
    have h10 : (1 / (N : ℝ)) * (N : ℝ) = 1 := by
      field_simp [hN_pos'.ne']
    have h9 : |(U.b : ℝ)| * (1 / (N : ℝ)) * (N : ℝ) = |(U.b : ℝ)| := by
      rw [mul_assoc, h10] <;> ring
    rw [h9] at h7
    linarith
  let aSet : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let bSet : Finset ℤ := Finset.Icc (-(3 * (N : ℤ))) (3 * (N : ℤ))
  have hS_sub : ∀ U ∈ S, U.a ∈ aSet ∧ U.b ∈ bSet := by
    intro U hU
    have ha : |(U.a : ℝ)| ≤ (N : ℝ) := ha_bound U hU
    have hb : |(U.b : ℝ)| ≤ (3 * N : ℝ) := hb_bound U hU
    have ha' : U.a ∈ aSet := by
      simp only [aSet, Finset.mem_Icc]
      have h11 : -(N : ℝ) ≤ (U.a : ℝ) := (abs_le.mp ha).1
      have h12 : (U.a : ℝ) ≤ (N : ℝ) := (abs_le.mp ha).2
      have h13 : -(N : ℤ) ≤ U.a := by exact_mod_cast h11
      have h14 : U.a ≤ (N : ℤ) := by exact_mod_cast h12
      exact ⟨h13, h14⟩
    have hb' : U.b ∈ bSet := by
      simp only [bSet, Finset.mem_Icc]
      have h11 : -(3 * (N : ℝ)) ≤ (U.b : ℝ) := (abs_le.mp hb).1
      have h12 : (U.b : ℝ) ≤ (3 * (N : ℝ)) := (abs_le.mp hb).2
      have h13 : -(3 * (N : ℤ)) ≤ U.b := by exact_mod_cast h11
      have h14 : U.b ≤ (3 * (N : ℤ)) := by exact_mod_cast h12
      exact ⟨h13, h14⟩
    exact ⟨ha', hb'⟩
  let boundSet : Finset (DyadicTube m) :=
    aSet.biUnion fun a => bSet.image fun b => ⟨a, b⟩
  have hS_bound : S ⊆ boundSet := by
    intro U hU
    rcases hS_sub U hU with ⟨ha, hb⟩
    simp only [boundSet, Finset.mem_biUnion]
    refine ⟨U.a, ha, ?_⟩
    simp only [Finset.mem_image]
    refine ⟨U.b, hb, ?_⟩
    cases U <;> rfl
  have h_card_bound : S.card ≤ boundSet.card := Finset.card_le_card hS_bound
  have h_boundSet_card : boundSet.card = aSet.card * bSet.card := by
    have h_disj : ∀ (a : ℤ), a ∈ aSet → ∀ (a' : ℤ), a' ∈ aSet → a ≠ a' →
        Disjoint (bSet.image (fun b : ℤ => (⟨a, b⟩ : DyadicTube m)))
          (bSet.image (fun b : ℤ => (⟨a', b⟩ : DyadicTube m))) := by
      intro a _ a' _ hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨b, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨b', _, h_eq⟩
      injection h_eq with h_a_eq _
      exact hne h_a_eq.symm
    rw [Finset.card_biUnion h_disj]
    have h_img_card : ∀ a ∈ aSet, (bSet.image (fun b : ℤ => (⟨a, b⟩ : DyadicTube m))).card = bSet.card := by
      intro a _
      rw [Finset.card_image_of_injective]
      <;> intro b1 b2 h <;> injection h <;> tauto
    rw [Finset.sum_congr rfl h_img_card]
    have h_sum : ∑ a ∈ aSet, bSet.card = aSet.card * bSet.card := by
      rw [Finset.sum_const]
      <;> rfl
    rw [h_sum, mul_comm]
  rw [h_boundSet_card] at h_card_bound
  have ha_card : aSet.card = 2 * N + 1 := by
    have h : (aSet.card : ℤ) = 2 * (N : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (-(N : ℤ)) (N : ℤ) (by omega)]
      <;> ring
    omega
  have hb_card : bSet.card = 6 * N + 1 := by
    have h : (bSet.card : ℤ) = 6 * (N : ℤ) + 1 := by
      rw [Int.card_Icc_of_le (-(3 * (N : ℤ))) (3 * (N : ℤ)) (by omega)]
      <;> ring
    omega
  rw [ha_card, hb_card] at h_card_bound
  have h_final : ((2 * N + 1) * (6 * N + 1) : ℝ) ≤ 100 * (N : ℝ)^2 := by
    have hN1 : (N : ℝ) ≥ 1 := by
      have h : 1 ≤ N := by omega
      exact_mod_cast h
    nlinarith
  have hδ2 : (dyadicDelta m)^(-2 : ℝ) = (N : ℝ)^2 := by
    rw [hδ_eq]
    have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast hN_pos
    have hpos : 0 < (1 / (N : ℝ)) := by positivity
    have h : (1 / (N : ℝ)) ^ (-2 : ℝ) = (N : ℝ)^2 := by
      rw [Real.rpow_neg hpos.le]
      have h2 : (1 / (N : ℝ)) ^ (2 : ℝ) = 1 / ((N : ℝ)^2) := by
        rw [Real.rpow_two]
        <;> field_simp [hN_pos'.ne'] <;> ring
      rw [h2]
      <;> field_simp [hN_pos'.ne'] <;> ring
    exact h
  have hS_card_le : (S.card : ℝ) ≤ ((2 * N + 1) * (6 * N + 1) : ℝ) := by
    exact_mod_cast h_card_bound
  rw [hδ2]
  exact le_trans hS_card_le h_final

/-! ========================================================================
   3. S-set transfer via centerRep isometry
   ======================================================================== -/

/-- Transfer IsFiniteDeltaSSet from the lifted family to the coarse family.

    Requires equality `S_lifted = image centerRep S_coarse`, which ensures
    every lifted element is a centerRep and every centerRep is lifted. -/
lemma sset_transfer_via_centerRep {n m : ℕ} (hnm : m ≤ n)
    {s C₂ Δ : ℝ} {S_lifted : Finset (DyadicTube n)}
    {S_coarse : Finset (DyadicTube m)}
    (h_eq2 : S_lifted = Finset.image (centerRep hnm) S_coarse)
    (h : IsFiniteDeltaSSet Δ s C₂ S_lifted) :
    IsFiniteDeltaSSet Δ s C₂ S_coarse := by
  have h_eq1 : S_coarse = Finset.image (sp hnm) S_lifted := by
    have h : Finset.image (sp hnm) S_lifted = S_coarse := by
      rw [h_eq2]
      ext U
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
        simpa [sourceParent_centerRep] using hx
      · intro hU
        refine ⟨centerRep hnm U, ⟨U, hU, rfl⟩, ?_⟩
        simp [sourceParent_centerRep]
    exact h.symm
  rcases h with ⟨h_nonempty, hδ_pos, hC_one, hs_nonneg, h_sep, h_growth⟩
  have h_inj : Set.InjOn (sp hnm) (S_lifted : Set (DyadicTube n)) := by
    intro c1 hc1 c2 hc2 h_eq_sp
    rw [h_eq2] at hc1 hc2
    rcases Finset.mem_image.mp hc1 with ⟨U1, _, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨U2, _, rfl⟩
    have h3 : U1 = U2 := by
      simpa [sourceParent_centerRep] using h_eq_sp
    rw [h3]
  have hS_coarse_nonempty : S_coarse.Nonempty := by
    rw [h_eq1]
    exact h_nonempty.image _
  have hS_coarse_sep : SeparatedAt Δ (S_coarse : Set (DyadicTube m)) := by
    intro U1 hU1 U2 hU2 hne
    have h1 : centerRep hnm U1 ∈ S_lifted := by
      rw [h_eq2]
      exact Finset.mem_image_of_mem _ hU1
    have h3 : centerRep hnm U2 ∈ S_lifted := by
      rw [h_eq2]
      exact Finset.mem_image_of_mem _ hU2
    have h5 : centerRep hnm U1 ≠ centerRep hnm U2 := by
      intro h6
      exact hne (centerRep_injective hnm h6)
    have h7 : Δ ≤ (centerRep hnm U1).dist (centerRep hnm U2) := h_sep h1 h3 h5
    rw [centerRep_dist_eq hnm U1 U2] at h7
    exact h7
  have h_growth' : ∀ (x : DyadicTube m) (r : ℝ), Δ ≤ r →
      ((S_coarse.filter fun y => y.dist x ≤ r).card : ℝ) ≤
        C₂ * r ^ s * (S_coarse.card : ℝ) := by
    intro x r hr
    let x' := centerRep hnm x
    have h_filter_eq : S_coarse.filter (fun y : DyadicTube m => y.dist x ≤ r) =
        Finset.image (sp hnm) (S_lifted.filter (fun y : DyadicTube n => y.dist x' ≤ r)) := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hU, hdist⟩
        have h1 : centerRep hnm U ∈ S_lifted := by
          rw [h_eq2]
          exact Finset.mem_image_of_mem _ hU
        have h3 : (centerRep hnm U).dist x' ≤ r := by
          rw [centerRep_dist_eq hnm U x]
          exact hdist
        refine ⟨centerRep hnm U, ⟨h1, h3⟩, ?_⟩
        simpa using sourceParent_centerRep hnm U
      · rintro ⟨c, ⟨hc, hdist⟩, h_sp_eq⟩
        have hU : sp hnm c ∈ S_coarse := by
          rw [h_eq1] <;> exact Finset.mem_image_of_mem _ hc
        have h4 : ∃ (V : DyadicTube m), V ∈ S_coarse ∧ c = centerRep hnm V := by
          have hc' : c ∈ S_lifted := hc
          rw [h_eq2] at hc'
          simp only [Finset.mem_image] at hc'
          rcases hc' with ⟨V, hV, rfl⟩
          exact ⟨V, hV, rfl⟩
        rcases h4 with ⟨V, hV, h_c_eq⟩
        have hV_eq_U : V = U := by
          have h1 : sp hnm c = U := h_sp_eq
          have h2 : sp hnm c = V := by
            rw [h_c_eq]
            exact sourceParent_centerRep hnm V
          rw [h2] at h1
          exact h1
        have h6 : V.dist x ≤ r := by
          have h7 : c.dist x' = V.dist x := by
            rw [h_c_eq]
            exact centerRep_dist_eq hnm V x
          rw [h7] at hdist
          exact hdist
        exact ⟨hV_eq_U ▸ hV, hV_eq_U ▸ h6⟩
    have h_card1 : (S_coarse.filter (fun y : DyadicTube m => y.dist x ≤ r)).card =
        (S_lifted.filter (fun y : DyadicTube n => y.dist x' ≤ r)).card := by
      rw [h_filter_eq]
      have h_inj' : Set.InjOn (sp hnm) ((S_lifted.filter (fun y : DyadicTube n => y.dist x' ≤ r)) : Set (DyadicTube n)) :=
        h_inj.mono (Finset.filter_subset _ _)
      rw [Finset.card_image_of_injOn h_inj']
    have h_card2 : (S_coarse.card : ℝ) = (S_lifted.card : ℝ) := by
      rw [h_eq1, Finset.card_image_of_injOn h_inj]
    rw [h_card1, h_card2]
    exact h_growth x' r hr
  exact ⟨hS_coarse_nonempty, hδ_pos, hC_one, hs_nonneg, hS_coarse_sep, h_growth'⟩

/-! ========================================================================
   4. Main typed QTTC theorem
   ======================================================================== -/

/-- QTTC assembly for typed dyadic tube families using sourceParent.

    Generalized to arbitrary point type α. Set α = Plane for A1/A2 integration,
    or α = DyadicSquare n for the original typed configuration. -/
theorem qttc_for_dyadicTubes (s : ℝ) (hs : 0 < s) (hs_lt_two : s < 2) :
    ∃ (A : ℝ), 1 ≤ A ∧
      ∀ {n m : ℕ} {α : Type*} [DecidableEq α]
        (hnm : m ≤ n) (hm_pos : 1 ≤ m)
        {C₁ : ℝ} {M : ℕ}
        {P : Finset α}
        {tubeFamily : α → Finset (DyadicTube n)},
        1 ≤ C₁ → P.Nonempty → 0 < M →
        (∀ p ∈ P, M / 2 < (tubeFamily p).card ∧ (tubeFamily p).card ≤ M) →
        (∀ p ∈ P, BallGrowth (dyadicDelta n) s C₁ (tubeFamily p)) →
        (∀ U ∈ globalCoarseG hnm P tubeFamily, |U.slope| ≤ 1) →
        (∀ U ∈ globalCoarseG hnm P tubeFamily, |U.intercept| ≤ 3) →
        ∃ (P' : Finset α)
          (T' : α → Finset (DyadicTube n))
          (C' : Finset (DyadicTube m))
          (K C₂ : ℝ) (H : ℕ),
          1 ≤ K ∧
          K ≤ A * Real.rpow (Real.log (2 / dyadicDelta m)) A ∧
          1 ≤ C₂ ∧ 0 < H ∧
          P' ⊆ P ∧
          (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
          (∀ p ∈ P', T' p ⊆ tubeFamily p) ∧
          (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
          IsFiniteDeltaSSet (dyadicDelta m) s C₂ C' ∧
          C₂ ≤ A * Real.rpow K A * C₁ ∧
          (∀ U ∈ C', (H : ℝ) ≤
            ∑ p ∈ P', (pointFiberG hnm T' p U).card) ∧
          (M : ℝ) * (P.card : ℝ) ≤
            K * (H : ℝ) * (C'.card : ℝ) ∧
          (H : ℝ) * (C'.card : ℝ) ≤
            K * (M : ℝ) * (P.card : ℝ) ∧
          C' ⊆ globalCoarseG hnm P tubeFamily := by
  let D : ℝ := 2
  let B : ℝ := 100
  have hD : 1 ≤ D := by norm_num
  have hB : 1 ≤ B := by norm_num
  have hsD : s ≤ D := by linarith
  rcases quantitative_thick_tube_cover s D B hs hsD hD hB with
    ⟨A, hA_one, hA_le, hQTTC⟩
  refine' ⟨A, hA_one, _⟩
  intro n m α _ hnm hm_pos C₁ M P tubeFamily hC1 hP_nonempty hM_pos
    h_size h_sset h_slope h_intercept
  set δ : ℝ := dyadicDelta n with hδ_def
  set Δ : ℝ := dyadicDelta m with hΔ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  have hδ_le_Δ : δ ≤ Δ := by
    have h1 : (n : ℕ) ≥ m := hnm
    have h2 : (2 : ℝ)^n ≥ (2 : ℝ)^m := by gcongr <;> omega
    have h3 : dyadicDelta n = 1 / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> norm_cast
    have h4 : dyadicDelta m = 1 / (2 : ℝ)^m := by
      simp [dyadicDelta] <;> norm_cast
    rw [hδ_def, hΔ_def, h3, h4]
    gcongr
  have hΔ_half : Δ ≤ 1 / 2 := by
    have h1 : dyadicDelta m = 1 / (2 : ℝ)^m := by
      simp [dyadicDelta] <;> norm_cast
    rw [hΔ_def, h1]
    have h2 : (2 : ℝ)^m ≥ 2 := by
      have h3 : m ≥ 1 := hm_pos
      have h4 : (2 : ℝ)^m ≥ (2 : ℝ)^1 := by gcongr
      norm_num at h4 ⊢ <;> exact h4
    have h5 : 1 / (2 : ℝ)^m ≤ 1 / 2 := by gcongr
    exact h5
  let coarse : DyadicTube n → DyadicTube n :=
    fun T => centerRep hnm (sp hnm T)
  let T_Delta := globalCoarseG hnm P tubeFamily
  let coarseRange : Finset (DyadicTube n) :=
    Finset.image (centerRep hnm) T_Delta
  let U_fine : Finset (DyadicTube n) := P.biUnion tubeFamily
  have hT_sub_U : ∀ p ∈ P, tubeFamily p ⊆ U_fine := by
    intro p hp T hT
    exact Finset.mem_biUnion.mpr ⟨p, hp, hT⟩
  have h_coarse_cover : ∀ T ∈ U_fine,
      coarse T ∈ coarseRange ∧ T.dist (coarse T) ≤ Δ := by
    intro T hT
    have h1 : sp hnm T ∈ T_Delta :=
      Finset.mem_image_of_mem (sp hnm) hT
    have h2 : coarse T ∈ coarseRange :=
      Finset.mem_image_of_mem (centerRep hnm) h1
    have h3 : T.dist (coarse T) ≤ Δ := centerRep_dist_bound hnm T
    exact ⟨h2, h3⟩
  have h_sep : SeparatedAt Δ (coarseRange : Set (DyadicTube n)) :=
    centerRep_separated hnm T_Delta
  have h_card : (coarseRange.card : ℝ) ≤ B * Δ ^ (-D) := by
    have h_inj : Function.Injective (centerRep hnm) := centerRep_injective hnm
    have h1 : coarseRange.card = T_Delta.card := by
      rw [Finset.card_image_of_injective _ h_inj]
    rw [h1]
    have h2 : (T_Delta.card : ℝ) ≤ 100 * Δ ^ (-2 : ℝ) :=
      dyadicTubes_bounded_card hm_pos T_Delta h_slope h_intercept
    simpa [B, D] using h2
  have h_main := hQTTC P U_fine tubeFamily coarse coarseRange
    hδ_pos hδ_le_Δ hΔ_half hC1 hP_nonempty hM_pos
    hT_sub_U h_size h_sset h_coarse_cover h_sep h_card
  rcases h_main with ⟨P', T', C'_lifted, K, C₂, H, hK_one, hK_eq, hK_bound,
    hC2_one, hH_pos, hP'_sub, hP_card, hT'_sub, hT'_size,
    hC'_eq, hC'_sub, hC'_sset, hC2_bound, hC2_exact,
    h_incidence, h_avg_lower, h_avg_upper⟩
  let C' : Finset (DyadicTube m) := Finset.image (sp hnm) C'_lifted
  have hC'_sub_TDelta : C' ⊆ T_Delta := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨c, hc, rfl⟩
    have h1 : c ∈ coarseRange := hC'_sub hc
    rcases Finset.mem_image.mp h1 with ⟨U2, hU2, h_eq⟩
    have h2 : sp hnm c = U2 := by
      have h3 : c = centerRep hnm U2 := h_eq.symm
      rw [h3]
      exact sourceParent_centerRep hnm U2
    rw [h2] <;> exact hU2
  have hC'_eq : C'_lifted = Finset.image (centerRep hnm) C' := by
    apply Finset.Subset.antisymm
    · -- C'_lifted ⊆ image centerRep C'
      intro c hc
      have h1 : c ∈ coarseRange := hC'_sub hc
      rcases Finset.mem_image.mp h1 with ⟨U, hU, h_eq⟩
      have hU' : U ∈ C' := by
        simp only [C', Finset.mem_image]
        refine ⟨c, hc, ?_⟩
        have h_sp : sp hnm c = U := by
          have h3 : c = centerRep hnm U := h_eq.symm
          rw [h3]
          exact sourceParent_centerRep hnm U
        exact h_sp
      have h_goal : c ∈ Finset.image (centerRep hnm) C' := by
        rw [←h_eq]
        exact Finset.mem_image_of_mem (centerRep hnm) hU'
      exact h_goal
    · -- image centerRep C' ⊆ C'_lifted
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨U, hU, rfl⟩
      rcases Finset.mem_image.mp hU with ⟨d, hd, h_sp_eq⟩
      have h_d_in_CR : d ∈ coarseRange := hC'_sub hd
      rcases Finset.mem_image.mp h_d_in_CR with ⟨V, hV, h_d_eq⟩
      have hV_eq : V = U := by
        have h_sp_d : sp hnm d = V := by
          have h3 : d = centerRep hnm V := h_d_eq.symm
          rw [h3]
          exact sourceParent_centerRep hnm V
        have h : sp hnm d = U := by simpa [h_d_eq] using h_sp_eq
        rw [h_sp_d] at h
        exact h
      rw [hV_eq] at h_d_eq
      exact h_d_eq ▸ hd
  have hC'_sset' : IsFiniteDeltaSSet Δ s C₂ C' :=
    sset_transfer_via_centerRep hnm hC'_eq hC'_sset
  have hC'_card : C'.card = C'_lifted.card := by
    have h_inj : Set.InjOn (sp hnm) (C'_lifted : Set (DyadicTube n)) := by
      intro c1 hc1 c2 hc2 h_eq
      have h1 : c1 ∈ coarseRange := hC'_sub hc1
      have h2 : c2 ∈ coarseRange := hC'_sub hc2
      rcases Finset.mem_image.mp h1 with ⟨U1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨U2, _, rfl⟩
      have h3 : U1 = U2 := by
        simpa [sourceParent_centerRep] using h_eq
      rw [h3]
    rw [Finset.card_image_of_injOn h_inj]
  have h_inc_transfer : ∀ (p : α) (U : DyadicTube m),
      qttcAssignedCount coarse T' p (centerRep hnm U) =
      (pointFiberG hnm T' p U).card := by
    intro p U
    have h_eq1 : ∀ T ∈ T' p, coarse T = centerRep hnm U ↔ sp hnm T = U := by
      intro T _
      have h_coarse_def : coarse T = centerRep hnm (sp hnm T) := by rfl
      constructor
      · intro h
        have h' : centerRep hnm (sp hnm T) = centerRep hnm U := by
          rwa [h_coarse_def] at h
        exact centerRep_injective hnm h'
      · intro h
        rw [h_coarse_def, h]
    have h_filter_eq : (T' p).filter (fun T => coarse T = centerRep hnm U) =
        (T' p).filter (fun T => sp hnm T = U) := by
      ext T
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hT, h⟩
        exact ⟨hT, (h_eq1 T hT).mp h⟩
      · rintro ⟨hT, h⟩
        exact ⟨hT, (h_eq1 T hT).mpr h⟩
    simp only [qttcAssignedCount, pointFiberG]
    rw [h_filter_eq]
  have h_incidence' : ∀ U ∈ C', (H : ℝ) ≤
      ∑ p ∈ P', (pointFiberG hnm T' p U).card := by
    intro U hU
    let c := centerRep hnm U
    have hc : c ∈ C'_lifted := by
      rw [hC'_eq]
      exact Finset.mem_image_of_mem _ hU
    have h_raw : H ≤ ∑ p ∈ P', ((T' p).filter fun ℓ => coarse ℓ = c).card := by
      have h := h_incidence c hc
      exact h
    have h_eq_sum : ∑ p ∈ P', ((T' p).filter fun ℓ => coarse ℓ = c).card =
        ∑ p ∈ P', (pointFiberG hnm T' p U).card := by
      apply Finset.sum_congr rfl
      intro p _
      have h_c_eq : c = centerRep hnm U := by rfl
      simpa [pointFiberG, h_c_eq] using h_inc_transfer p U
    rw [h_eq_sum] at h_raw
    exact_mod_cast h_raw
  have h_avg_lower' : (M : ℝ) * (P.card : ℝ) ≤
      K * (H : ℝ) * (C'.card : ℝ) := by
    rw [hC'_card] at *
    <;> exact h_avg_lower
  have h_avg_upper' : (H : ℝ) * (C'.card : ℝ) ≤
      K * (M : ℝ) * (P.card : ℝ) := by
    rw [hC'_card] at *
    <;> exact h_avg_upper
  exact ⟨P', T', C', K, C₂, H, hK_one, hK_bound, hC2_one, hH_pos,
    hP'_sub, hP_card, hT'_sub, hT'_size, hC'_sset', hC2_bound,
    h_incidence', h_avg_lower', h_avg_upper', hC'_sub_TDelta⟩

end DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly

end
