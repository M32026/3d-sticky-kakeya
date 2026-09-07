module

/-
  Global slope partition for the NiceConfiguration bridge (CORRECTED).

  Partitions the POINT SET P into CP-flat-dominant and CP-steep-dominant
  classes, retains one class with comparable covering mass, and applies
  ONE global coordinate swap if the CP-flat class is retained.

  CRITICAL orientation note:
  - CoordinatePartition "flat" = v1≠0, |affineLineParams.1|≤1 (x=ay+b)
  - Snap-flat (for snap transfer) = v0≠0, |affineLineSlopeIntercept.1|≤1 (y=mx+c)
  - CP-flat + swap → snap-flat
  - CP-steep (no swap) → snap-flat

  Therefore: CP-flat dominates → swap=true; CP-steep dominates → swap=false.

  Output S-set constant: (C_T * Kpack) * 2 * Kpack
  Requires hδ_slope : δ^ρ_slope ≤ 1/2 for mass retention with c_slope = 1/2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open CoordinatePartition
open DiscretisedFurstenbergEstimate.CoveringUtils

/-- Ncover abbreviation. -/
abbrev ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-- Extract slope from affineLineParams when v1 ≠ 0. -/
lemma affineLineParams_slope {ℓ : AffineLine} (h : (LemmaE.getDirV ℓ) 1 ≠ 0) :
    (LemmaE.affineLineParams ℓ).1 = (LemmaE.getDirV ℓ) 0 / (LemmaE.getDirV ℓ) 1 := by
  let v := LemmaE.getDirV ℓ
  let off := ℓ.offset
  let a := if v 1 = 0 then (0 : ℝ) else v 0 / v 1
  let b := off 0 - a * off 1
  have h_def : LemmaE.affineLineParams ℓ = (a, b) := by
    unfold LemmaE.affineLineParams
    <;> rfl
  rw [h_def]
  have ha : a = v 0 / v 1 := by
    dsimp only [a]
    rw [if_neg h]
    <;> rfl
  rw [ha]
  <;> rfl

/-- Extract slope from affineLineSlopeIntercept when v0 ≠ 0. -/
lemma affineLineSlopeIntercept_slope {ℓ : AffineLine} (h : (LemmaE.getDirV ℓ) 0 ≠ 0) :
    (affineLineSlopeIntercept ℓ).1 = (LemmaE.getDirV ℓ) 1 / (LemmaE.getDirV ℓ) 0 := by
  let v := LemmaE.getDirV ℓ
  let off := ℓ.offset
  let m := v 1 / v 0
  let c := off 1 - m * off 0
  have h_def : affineLineSlopeIntercept ℓ = (m, c) := by
    unfold affineLineSlopeIntercept
    rw [dif_neg h]
    <;> rfl
  rw [h_def]
  <;> rfl

/-- Direction vector relation under swapLine:
    ∃ c ≠ 0, (getDirV (swapLine ℓ)) 0 = c * (getDirV ℓ) 1
             and (getDirV (swapLine ℓ)) 1 = c * (getDirV ℓ) 0. -/
lemma swapLine_dirV_relation (ℓ : AffineLine) :
    ∃ (c : ℝ), c ≠ 0 ∧
      (LemmaE.getDirV (swapLine ℓ)) 0 = c * (LemmaE.getDirV ℓ) 1 ∧
      (LemmaE.getDirV (swapLine ℓ)) 1 = c * (LemmaE.getDirV ℓ) 0 := by
  let v := LemmaE.getDirV ℓ
  let v' := LemmaE.getDirV (swapLine ℓ)
  have hv_ne : v ≠ 0 := (LemmaE.getDirV_spec ℓ).2
  have hv'_ne : v' ≠ 0 := (LemmaE.getDirV_spec (swapLine ℓ)).2
  have h_dir_eq : (swapLine ℓ).1.direction =
      Submodule.map (swapCoordsLI : Plane →ₗ[ℝ] Plane) ℓ.1.direction :=
    AffineSubspace.map_direction (swapCoordsLI.toLinearEquiv.toAffineMap) ℓ.1
  have h_span : ℓ.1.direction = ℝ ∙ v :=
    direction_eq_span ℓ.2 (LemmaE.getDirV_spec ℓ).1 hv_ne
  have h_map : Submodule.map (swapCoordsLI : Plane →ₗ[ℝ] Plane) (ℝ ∙ v) = ℝ ∙ swapCoords v := by
    have h1 : Submodule.map (swapCoordsLI : Plane →ₗ[ℝ] Plane) (Submodule.span ℝ {v}) =
        Submodule.span ℝ ((swapCoordsLI : Plane →ₗ[ℝ] Plane) '' {v}) :=
      Submodule.map_span _ _
    have h2 : (swapCoordsLI : Plane →ₗ[ℝ] Plane) '' {v} = {swapCoords v} := by
      have h21 : (swapCoordsLI : Plane →ₗ[ℝ] Plane) v = swapCoords v := by
        simp [swapCoordsLI]
      ext x
      simp [h21]
      <;> tauto
    rw [h1, h2] <;> rfl
  have h_span' : (swapLine ℓ).1.direction = ℝ ∙ swapCoords v := by
    rw [h_dir_eq, h_span]
    exact h_map
  have hv'_in : v' ∈ (swapLine ℓ).1.direction := (LemmaE.getDirV_spec (swapLine ℓ)).1
  rw [h_span'] at hv'_in
  have h_exists : ∃ (c : ℝ), c • swapCoords v = v' := by
    rwa [Submodule.mem_span_singleton] at hv'_in
  rcases h_exists with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    by_contra hc0
    rw [hc0, zero_smul] at hc
    exact hv'_ne hc.symm
  have hvc : v' = c • swapCoords v := hc.symm
  have h_swap0 : ∀ (x : Plane), (swapCoords x) 0 = x 1 := by
    intro x
    simp [swapCoords]
    <;> fin_cases i <;> simp
  have h_swap1 : ∀ (x : Plane), (swapCoords x) 1 = x 0 := by
    intro x
    simp [swapCoords]
    <;> fin_cases i <;> simp
  have h_v'0 : v' 0 = c * v 1 := by
    rw [hvc]
    have h : (c • swapCoords v) 0 = c * (swapCoords v) 0 := Pi.smul_apply c (swapCoords v) 0
    rw [h, h_swap0]
  have h_v'1 : v' 1 = c * v 0 := by
    rw [hvc]
    have h : (c • swapCoords v) 1 = c * (swapCoords v) 1 := Pi.smul_apply c (swapCoords v) 1
    rw [h, h_swap1]
  exact ⟨c, hc_ne, h_v'0, h_v'1⟩

/-- CP-flat line, after swapLine, is snap-flat (v0≠0, |slope|≤1 in y=mx+c). -/
lemma cp_flat_swap_snap_flat (ℓ : AffineLine)
    (h_flat : (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |(LemmaE.affineLineParams ℓ).1| ≤ 1) :
    (LemmaE.getDirV (swapLine ℓ)) 0 ≠ 0 ∧
    |(affineLineSlopeIntercept (swapLine ℓ)).1| ≤ 1 := by
  rcases swapLine_dirV_relation ℓ with ⟨c, hc_ne, h_v'0, h_v'1⟩
  let v := LemmaE.getDirV ℓ
  let v' := LemmaE.getDirV (swapLine ℓ)
  have h_v1_ne : v 1 ≠ 0 := h_flat.1
  have h_v'0_ne : v' 0 ≠ 0 := by
    rw [h_v'0] <;> exact mul_ne_zero hc_ne h_v1_ne
  have h_a_eq : (LemmaE.affineLineParams ℓ).1 = v 0 / v 1 := affineLineParams_slope h_v1_ne
  have h_slope_eq : (affineLineSlopeIntercept (swapLine ℓ)).1 = v' 1 / v' 0 := affineLineSlopeIntercept_slope h_v'0_ne
  have h_final : (affineLineSlopeIntercept (swapLine ℓ)).1 = v 0 / v 1 := by
    rw [h_slope_eq, h_v'1, h_v'0]
    have h_goal : (c * v 0) / (c * v 1) = v 0 / v 1 := by
      field_simp [hc_ne, h_v1_ne] <;> ring
    exact h_goal
  have h_abs : |(affineLineSlopeIntercept (swapLine ℓ)).1| ≤ 1 := by
    rw [h_final]
    have h9 : v 0 / v 1 = (LemmaE.affineLineParams ℓ).1 := h_a_eq.symm
    rw [h9]
    exact h_flat.2
  exact ⟨h_v'0_ne, h_abs⟩

/-- CP-steep line is snap-flat (v0≠0, |slope|≤1 in y=mx+c) without swap. -/
lemma cp_steep_snap_flat (ℓ : AffineLine)
    (h_steep : (LemmaE.getDirV ℓ) 1 = 0 ∨ |(LemmaE.affineLineParams ℓ).1| > 1) :
    (LemmaE.getDirV ℓ) 0 ≠ 0 ∧
    |(affineLineSlopeIntercept ℓ).1| ≤ 1 := by
  let v := LemmaE.getDirV ℓ
  have hv_ne : v ≠ 0 := (LemmaE.getDirV_spec ℓ).2
  cases h_steep with
  | inl h_v1_eq =>
    have h_v0_ne : v 0 ≠ 0 := by
      by_contra h
      have h_v_eq : v = 0 := by
        ext i
        fin_cases i <;> simp [h, h_v1_eq] <;> linarith
      exact hv_ne h_v_eq
    have h_slope_eq : (affineLineSlopeIntercept ℓ).1 = 0 := by
      rw [affineLineSlopeIntercept_slope h_v0_ne, h_v1_eq]
      <;> ring
    rw [h_slope_eq]
    exact ⟨h_v0_ne, by norm_num⟩
  | inr h_abs_gt =>
    have h_v1_ne : v 1 ≠ 0 := by
      by_contra h
      have h_a_eq : (LemmaE.affineLineParams ℓ).1 = 0 := by
        let v := LemmaE.getDirV ℓ
        let off := ℓ.offset
        let a := if v 1 = 0 then (0 : ℝ) else v 0 / v 1
        let b := off 0 - a * off 1
        have h_def : LemmaE.affineLineParams ℓ = (a, b) := by
          unfold LemmaE.affineLineParams <;> rfl
        rw [h_def]
        have ha : a = 0 := by
          dsimp only [a]
          rw [if_pos h]
          <;> rfl
        rw [ha]
        <;> rfl
      rw [h_a_eq] at h_abs_gt
      <;> norm_num at h_abs_gt <;> linarith
    have h_a_eq : (LemmaE.affineLineParams ℓ).1 = v 0 / v 1 := affineLineParams_slope h_v1_ne
    have h_v0_ne : v 0 ≠ 0 := by
      by_contra h
      rw [h_a_eq, h, zero_div] at h_abs_gt
      <;> norm_num at h_abs_gt <;> linarith
    have h_slope_eq : (affineLineSlopeIntercept ℓ).1 = v 1 / v 0 := affineLineSlopeIntercept_slope h_v0_ne
    have h10 : |v 1| ≤ |v 0| := by
      have h9 : |v 0 / v 1| > 1 := by
        rw [h_a_eq] at h_abs_gt <;> exact h_abs_gt
      have h11 : |v 0 / v 1| = |v 0| / |v 1| := by rw [abs_div]
      rw [h11] at h9
      have h12 : 0 < |v 1| := abs_pos.mpr h_v1_ne
      have h13 : |v 0| > |v 1| := by
        calc
          |v 0| = (|v 0| / |v 1|) * |v 1| := by field_simp <;> ring
          _ > 1 * |v 1| := by gcongr
          _ = |v 1| := by ring
      exact h13.le
    have h_abs : |v 1 / v 0| ≤ 1 := by
      have h14 : |v 1 / v 0| = |v 1| / |v 0| := by rw [abs_div]
      rw [h14]
      have h15 : 0 < |v 0| := abs_pos.mpr h_v0_ne
      exact (div_le_one h15).mpr h10
    rw [h_slope_eq]
    exact ⟨h_v0_ne, h_abs⟩

/-- Global slope partition with orientation. -/
lemma global_slope_partition
    (δ s C_T : ℝ)
    (hs_pos : 0 < s)
    (hCT_pos : 0 < C_T)
    (hδ_pos : 0 < δ)
    (P : Set Plane)
    (T : Set AffineLine)
    (F : ∀ (p : Plane), p ∈ P → Finset AffineLine)
    (hF_sub : ∀ p hp, (F p hp : Set AffineLine) ⊆ T)
    (hF_sset : ∀ p hp, IsDeltaSSet δ s (C_T * (MainAppendix.affineLine_packing_constant : ℝ)) (F p hp : Set AffineLine))
    (hF_sep : ∀ p hp, Set.Pairwise (F p hp : Set AffineLine) (fun x y => δ ≤ dist x y))
    (hF_near : ∀ p hp, ∀ ℓ ∈ F p hp, p ∈ Metric.cthickening δ ℓ.1)
    (ρ_slope : ℝ)
    (hρ_slope_nonneg : 0 ≤ ρ_slope)
    (hδ_slope : δ ^ ρ_slope ≤ 1 / 2) :
    ∃ (swapped : Bool) (P' : Set Plane)
      (P_oriented : Set Plane) (T_oriented : Set AffineLine)
      (F_oriented : ∀ (p : Plane), p ∈ P_oriented → Finset AffineLine)
      (c_slope : ℝ),
      0 < c_slope ∧
      c_slope = 1 / 2 ∧
      P' ⊆ P ∧
      (swapped = false → P_oriented = P' ∧ T_oriented = T) ∧
      (swapped = true → P_oriented = swapCoords '' P' ∧ T_oriented = swapLine '' T) ∧
      (ncover δ T_oriented : ENNReal) = (ncover δ T : ENNReal) ∧
      (∀ p hp, (F_oriented p hp : Set AffineLine) ⊆ T_oriented) ∧
      (∀ p hp, IsDeltaSSet δ s
        ((C_T * (MainAppendix.affineLine_packing_constant : ℝ)) * 2 * (MainAppendix.affineLine_packing_constant : ℝ))
        (F_oriented p hp : Set AffineLine)) ∧
      (∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → (LemmaE.getDirV ℓ) 0 ≠ 0) ∧
      (∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → |(affineLineSlopeIntercept ℓ).1| ≤ 1) ∧
      (∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → p ∈ Metric.cthickening δ ℓ.1) ∧
      c_slope ≥ δ ^ ρ_slope ∧
      (ncover δ P_oriented : ENNReal) ≥ ENNReal.ofReal c_slope * (ncover δ P : ENNReal) := by
  let Kpack : ℝ := (MainAppendix.affineLine_packing_constant : ℝ)
  have hKpack_pos : 0 < Kpack := by
    have h : 0 < MainAppendix.affineLine_packing_constant := MainAppendix.affineLine_packing_constant_pos
    have h' : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := Nat.cast_pos.mpr h
    simpa [Kpack] using h'
  let C_in : ℝ := C_T * Kpack
  let C_out : ℝ := C_in * 2 * Kpack
  have hC_in_pos : 0 < C_in := by positivity
  have hC_out_pos : 0 < C_out := by positivity

  let flat_cond (ℓ : AffineLine) : Prop :=
    (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |(LemmaE.affineLineParams ℓ).1| ≤ 1
  let steep_cond (ℓ : AffineLine) : Prop :=
    (LemmaE.getDirV ℓ) 1 = 0 ∨ |(LemmaE.affineLineParams ℓ).1| > 1

  let flatFiber (p : Plane) : Finset AffineLine :=
    if h : p ∈ P then (F p h).filter flat_cond else ∅
  let steepFiber (p : Plane) : Finset AffineLine :=
    if h : p ∈ P then (F p h).filter steep_cond else ∅

  have h_flatFiber_def : ∀ (p : Plane) (hp : p ∈ P),
      flatFiber p = (F p hp).filter flat_cond := by
    intro p hp
    simp [flatFiber, hp] <;> rfl
  have h_steepFiber_def : ∀ (p : Plane) (hp : p ∈ P),
      steepFiber p = (F p hp).filter steep_cond := by
    intro p hp
    simp [steepFiber, hp] <;> rfl

  have h_partition : ∀ (p : Plane) (hp : p ∈ P),
      (flatFiber p) ∪ (steepFiber p) = F p hp ∧
      Disjoint (flatFiber p) (steepFiber p) ∧
      (2 * (flatFiber p).card ≥ (F p hp).card ∨ 2 * (steepFiber p).card ≥ (F p hp).card) := by
    intro p hp
    rcases partition_half (T := F p hp) with ⟨T_flat, T_steep, h_union, h_disj, h_flat_prop, h_steep_prop, h_half⟩
    have h_flat_sub : T_flat ⊆ F p hp := by
      have h : T_flat ⊆ T_flat ∪ T_steep := by simp
      rw [h_union] at h; exact h
    have h_steep_sub : T_steep ⊆ F p hp := by
      have h : T_steep ⊆ T_flat ∪ T_steep := by simp
      rw [h_union] at h; exact h
    have h_flat_eq2 : flatFiber p = T_flat := by
      rw [h_flatFiber_def p hp]
      apply Finset.ext
      intro ℓ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h_in, h_cond⟩
        have h_in_union : ℓ ∈ T_flat ∪ T_steep := by rw [h_union]; exact h_in
        have h_cases : ℓ ∈ T_flat ∨ ℓ ∈ T_steep := Finset.mem_union.mp h_in_union
        cases h_cases with
        | inl h => exact h
        | inr h =>
          have h_steep_cond := h_steep_prop ℓ h
          rcases h_steep_cond with (h_v1_eq | h_abs_gt)
          · exact (h_cond.1 h_v1_eq).elim
          · linarith [h_cond.2]
      · intro h_in_Tflat
        have h_in : ℓ ∈ F p hp := h_flat_sub h_in_Tflat
        have h_cond := h_flat_prop ℓ h_in_Tflat
        exact ⟨h_in, h_cond⟩
    have h_steep_eq2 : steepFiber p = T_steep := by
      rw [h_steepFiber_def p hp]
      apply Finset.ext
      intro ℓ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h_in, h_cond⟩
        have h_in_union : ℓ ∈ T_flat ∪ T_steep := by rw [h_union]; exact h_in
        have h_cases : ℓ ∈ T_flat ∨ ℓ ∈ T_steep := Finset.mem_union.mp h_in_union
        cases h_cases with
        | inl h =>
          have h_flat_cond := h_flat_prop ℓ h
          rcases h_cond with (h_v1_eq | h_abs_gt)
          · exact (h_flat_cond.1 h_v1_eq).elim
          · linarith [h_flat_cond.2]
        | inr h => exact h
      · intro h_in_Tsteep
        have h_in : ℓ ∈ F p hp := h_steep_sub h_in_Tsteep
        have h_cond := h_steep_prop ℓ h_in_Tsteep
        exact ⟨h_in, h_cond⟩
    rw [h_flat_eq2, h_steep_eq2]
    exact ⟨h_union, h_disj, h_half⟩

  let P_flat : Set Plane := {p | ∃ (hp : p ∈ P), 2 * (flatFiber p).card ≥ (F p hp).card}
  let P_steep : Set Plane := {p | ∃ (hp : p ∈ P), 2 * (steepFiber p).card ≥ (F p hp).card}

  have hP_flat_sub : P_flat ⊆ P := by
    intro p hp
    rcases hp with ⟨hp, _⟩
    exact hp
  have hP_steep_sub : P_steep ⊆ P := by
    intro p hp
    rcases hp with ⟨hp, _⟩
    exact hp

  have h_union : P_flat ∪ P_steep = P := by
    ext p
    simp only [P_flat, P_steep, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have h := (h_partition p hp).2.2
      cases h with
      | inl hflat => exact Or.inl ⟨hp, hflat⟩
      | inr hsteep => exact Or.inr ⟨hp, hsteep⟩

  have h_ncover_union : ncover δ P ≤ ncover δ P_flat + ncover δ P_steep := by
    have h : Metric.externalCoveringNumber δ.toNNReal (P_flat ∪ P_steep) ≤
        Metric.externalCoveringNumber δ.toNNReal P_flat +
        Metric.externalCoveringNumber δ.toNNReal P_steep :=
      externalCoveringNumber_union (ε := δ.toNNReal)
    have h' : ncover δ (P_flat ∪ P_steep) ≤ ncover δ P_flat + ncover δ P_steep := by
      exact_mod_cast h
    rw [h_union] at h'
    exact h'

  -- Helper: multiply both sides by 1/2 in ENNReal
  have h_half_mul : ∀ (x y : ENNReal), x ≤ 2 * y → ENNReal.ofReal (1 / 2 : ℝ) * x ≤ y := by
    intro x y h
    have h4 : ENNReal.ofReal (1 / 2 : ℝ) * x ≤ ENNReal.ofReal (1 / 2 : ℝ) * (2 * y) := by gcongr
    have h5 : ENNReal.ofReal (1 / 2 : ℝ) * (2 * y) = y := by
      have h6 : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal) = 1 := by
        have h7 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        rw [h7]
        have h8 : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 : ℝ) = 1 := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          <;> norm_num
        exact h8
      calc
        ENNReal.ofReal (1 / 2 : ℝ) * (2 * y)
          = (ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal)) * y := by ring
        _ = (1 : ENNReal) * y := by rw [h6]
        _ = y := by rw [one_mul]
    rw [h5] at h4
    exact h4

  by_cases h_flat_dominates : ncover δ P_flat ≥ ncover δ P_steep
  · -- Case 1: CP-flat dominates → swap = true
    have h_ratio : ncover δ P ≤ (2 : ENNReal) * ncover δ P_flat := by
      calc ncover δ P
        ≤ ncover δ P_flat + ncover δ P_steep := h_ncover_union
      _ ≤ ncover δ P_flat + ncover δ P_flat := by gcongr
      _ = 2 * ncover δ P_flat := by ring
    have hP_flat_mass : ncover δ P_flat ≥ ENNReal.ofReal (1 / 2 : ℝ) * ncover δ P :=
      h_half_mul (ncover δ P) (ncover δ P_flat) h_ratio

    let P' := P_flat
    let P_oriented := swapCoords '' P'
    let T_oriented := swapLine '' T
    let F_oriented : ∀ (p : Plane), p ∈ P_oriented → Finset AffineLine :=
      fun p _ => (flatFiber (swapCoords p)).image swapLine
    let c_slope : ℝ := 1 / 2

    have h_ncover_T : ncover δ T_oriented = ncover δ T := by
      have h := externalCoveringNumber_image_of_involutive_isometry
        swapLine_isometry swapLine_invol δ.toNNReal T
      exact_mod_cast h
    have h_ncover_P : ncover δ P_oriented = ncover δ P' := by
      have h := externalCoveringNumber_image_of_involutive_isometry
        swapCoords_isometry swapCoords_invol δ.toNNReal P'
      exact_mod_cast h

    have h1_pos : 0 < c_slope := by norm_num [c_slope]
    have h2_sub : P' ⊆ P := hP_flat_sub
    have h3_false : (true = false → P_oriented = P' ∧ T_oriented = T) := by
      intro h
      simp at h
    have h4_true : (true = true → P_oriented = swapCoords '' P' ∧ T_oriented = swapLine '' T) := by
      intro h
      exact ⟨rfl, rfl⟩
    have h5_ncover : ncover δ T_oriented = ncover δ T := h_ncover_T
    have h6_sub : ∀ p hp, (F_oriented p hp : Set AffineLine) ⊆ T_oriented := by
      intro p hp
      let q := swapCoords p
      have hq_P' : q ∈ P' := by
        have h_img : p ∈ swapCoords '' P' := hp
        rcases h_img with ⟨q', hq', h_eq⟩
        have hq_eq : q = q' := by
          have h10 : swapCoords p = swapCoords (swapCoords q') := by
            rw [h_eq.symm]
          have h11 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
          rw [h11] at h10
          exact h10
        rw [hq_eq]
        exact hq'
      have hq_P : q ∈ P := hP_flat_sub hq_P'
      have h1 : (flatFiber q : Set AffineLine) ⊆ (F q hq_P : Set AffineLine) := by
        rw [h_flatFiber_def q hq_P] <;> exact Finset.filter_subset _ _
      have h2 : (flatFiber q : Set AffineLine) ⊆ T := Set.Subset.trans h1 (hF_sub q hq_P)
      have h3 : (F_oriented p hp : Set AffineLine) = swapLine '' (flatFiber q : Set AffineLine) := by
        simp [F_oriented, Finset.coe_image] <;> rfl
      rw [h3]
      exact Set.image_mono h2
    have h7_sset : ∀ p hp, IsDeltaSSet δ s C_out (F_oriented p hp : Set AffineLine) := by
      intro p hp
      let q := swapCoords p
      have hq_P' : q ∈ P' := by
        have h_img : p ∈ swapCoords '' P' := hp
        rcases h_img with ⟨q', hq', h_eq⟩
        have hq_eq : q = q' := by
          have h10 : swapCoords p = swapCoords (swapCoords q') := by
            rw [h_eq.symm]
          have h11 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
          rw [h11] at h10
          exact h10
        rw [hq_eq]; exact hq'
      rcases hq_P' with ⟨hq_P, h_half⟩
      have h_flat_sub : flatFiber q ⊆ F q hq_P := by
        rw [h_flatFiber_def q hq_P] <;> exact Finset.filter_subset _ _
      have h_flat_sep : Set.Pairwise (flatFiber q : Set AffineLine) (fun x y => δ ≤ dist x y) :=
        (hF_sep q hq_P).mono (by exact_mod_cast h_flat_sub)
      have h_flat_nonempty : (flatFiber q).Nonempty := by
        by_contra h
        have h' : (flatFiber q).card = 0 := by simpa using h
        rw [h'] at h_half
        have hT_card : (F q hq_P).card = 0 := by linarith
        have hT_empty : F q hq_P = ∅ := Finset.card_eq_zero.mp hT_card
        have h_sset := hF_sset q hq_P
        rw [hT_empty] at h_sset
        have h_false : False := by
          simpa [Set.nonempty_iff_ne_empty] using h_sset.1
        exact h_false
      have h_sset_flat : IsDeltaSSet δ s C_out (flatFiber q : Set AffineLine) :=
        large_separated_subset_sset hδ_pos (by linarith) hC_in_pos
          (hF_sset q hq_P) h_flat_sub h_flat_sep h_flat_nonempty h_half
      have h4 : (F_oriented p hp : Set AffineLine) = swapLine '' (flatFiber q : Set AffineLine) := by
        simp [F_oriented, Finset.coe_image] <;> rfl
      rw [h4]
      exact swapLine_sset h_sset_flat
    have h8_v0 : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → (LemmaE.getDirV ℓ) 0 ≠ 0 := by
      intro p hp ℓ hℓ
      let q := swapCoords p
      rcases Finset.mem_image.mp hℓ with ⟨ℓ0, hℓ0, rfl⟩
      have hq_P' : q ∈ P' := by
        have h_img : p ∈ swapCoords '' P' := hp
        rcases h_img with ⟨q', hq', h_eq⟩
        have hq_eq : q = q' := by
          have h10 : swapCoords p = swapCoords (swapCoords q') := by
            rw [h_eq.symm]
          have h11 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
          rw [h11] at h10
          exact h10
        rw [hq_eq]; exact hq'
      rcases hq_P' with ⟨hq_P, _⟩
      have h_flat_cond : flat_cond ℓ0 := by
        rw [h_flatFiber_def q hq_P] at hℓ0
        exact (Finset.mem_filter.mp hℓ0).2
      exact (cp_flat_swap_snap_flat ℓ0 h_flat_cond).1
    have h9_slope : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → |(affineLineSlopeIntercept ℓ).1| ≤ 1 := by
      intro p hp ℓ hℓ
      let q := swapCoords p
      rcases Finset.mem_image.mp hℓ with ⟨ℓ0, hℓ0, rfl⟩
      have hq_P' : q ∈ P' := by
        have h_img : p ∈ swapCoords '' P' := hp
        rcases h_img with ⟨q', hq', h_eq⟩
        have hq_eq : q = q' := by
          have h10 : swapCoords p = swapCoords (swapCoords q') := by
            rw [h_eq.symm]
          have h11 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
          rw [h11] at h10
          exact h10
        rw [hq_eq]; exact hq'
      rcases hq_P' with ⟨hq_P, _⟩
      have h_flat_cond : flat_cond ℓ0 := by
        rw [h_flatFiber_def q hq_P] at hℓ0
        exact (Finset.mem_filter.mp hℓ0).2
      exact (cp_flat_swap_snap_flat ℓ0 h_flat_cond).2
    have h10_near : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → p ∈ Metric.cthickening δ ℓ.1 := by
      intro p hp ℓ hℓ
      let q := swapCoords p
      rcases Finset.mem_image.mp hℓ with ⟨ℓ0, hℓ0, rfl⟩
      have hq_P' : q ∈ P' := by
        have h_img : p ∈ swapCoords '' P' := hp
        rcases h_img with ⟨q', hq', h_eq⟩
        have hq_eq : q = q' := by
          have h10 : swapCoords p = swapCoords (swapCoords q') := by
            rw [h_eq.symm]
          have h11 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
          rw [h11] at h10
          exact h10
        rw [hq_eq]; exact hq'
      rcases hq_P' with ⟨hq_P, _⟩
      have hℓ_in_F : ℓ0 ∈ F q hq_P := by
        rw [h_flatFiber_def q hq_P] at hℓ0
        exact (Finset.mem_filter.mp hℓ0).1
      have h_near_orig : q ∈ Metric.cthickening δ ℓ0.1 := hF_near q hq_P ℓ0 hℓ_in_F
      have h5 := swapLine_near h_near_orig
      have h6 : swapCoords q = p := by
        have h7 : q = swapCoords p := by rfl
        rw [h7]
        exact swapCoords_invol p
      rw [h6] at h5
      exact h5
    have h11_cslope : c_slope ≥ δ ^ ρ_slope := by
      simpa [c_slope] using hδ_slope
    have h12_mass : ncover δ P_oriented ≥ ENNReal.ofReal c_slope * ncover δ P := by
      have h5 : ncover δ P_oriented = ncover δ P' := h_ncover_P
      rw [h5]
      have h6 : ncover δ P' ≥ ENNReal.ofReal c_slope * ncover δ P := by
        simpa [c_slope] using hP_flat_mass
      exact h6
    have h_cslope_eq : c_slope = 1 / 2 := by simp [c_slope]
    exact ⟨true, P', P_oriented, T_oriented, F_oriented, c_slope,
      h1_pos, h_cslope_eq, h2_sub, h3_false, h4_true, h5_ncover, h6_sub, h7_sset, h8_v0, h9_slope, h10_near, h11_cslope, h12_mass⟩

  · -- Case 2: CP-steep dominates → swap = false
    have h_steep_dominates : ncover δ P_steep > ncover δ P_flat :=
      lt_of_not_ge h_flat_dominates
    have h_ratio : ncover δ P ≤ (2 : ENNReal) * ncover δ P_steep := by
      calc ncover δ P
        ≤ ncover δ P_flat + ncover δ P_steep := h_ncover_union
      _ ≤ ncover δ P_steep + ncover δ P_steep := by gcongr <;> linarith
      _ = 2 * ncover δ P_steep := by ring
    have hP_steep_mass : ncover δ P_steep ≥ ENNReal.ofReal (1 / 2 : ℝ) * ncover δ P :=
      h_half_mul (ncover δ P) (ncover δ P_steep) h_ratio

    let P' := P_steep
    let P_oriented := P'
    let T_oriented := T
    let F_oriented : ∀ (p : Plane), p ∈ P_oriented → Finset AffineLine :=
      fun p _ => steepFiber p
    let c_slope : ℝ := 1 / 2

    have h1_pos : 0 < c_slope := by norm_num [c_slope]
    have h2_sub : P' ⊆ P := hP_steep_sub
    have h3_false : (false = false → P_oriented = P' ∧ T_oriented = T) := by
      intro h
      exact ⟨rfl, rfl⟩
    have h4_true : (false = true → P_oriented = swapCoords '' P' ∧ T_oriented = swapLine '' T) := by
      intro h
      simp at h
    have h5_ncover : ncover δ T_oriented = ncover δ T := by rfl
    have h6_sub : ∀ p hp, (F_oriented p hp : Set AffineLine) ⊆ T_oriented := by
      intro p hp
      rcases hp with ⟨hp_P, _⟩
      have h1 : (steepFiber p : Set AffineLine) ⊆ (F p hp_P : Set AffineLine) := by
        rw [h_steepFiber_def p hp_P] <;> exact Finset.filter_subset _ _
      have h2 : (steepFiber p : Set AffineLine) ⊆ T := Set.Subset.trans h1 (hF_sub p hp_P)
      simpa [F_oriented, T_oriented] using h2
    have h7_sset : ∀ p hp, IsDeltaSSet δ s C_out (F_oriented p hp : Set AffineLine) := by
      intro p hp
      rcases hp with ⟨hp_P, h_half⟩
      have h_steep_sub : steepFiber p ⊆ F p hp_P := by
        rw [h_steepFiber_def p hp_P] <;> exact Finset.filter_subset _ _
      have h_steep_sep : Set.Pairwise (steepFiber p : Set AffineLine) (fun x y => δ ≤ dist x y) :=
        (hF_sep p hp_P).mono (by exact_mod_cast h_steep_sub)
      have h_steep_nonempty : (steepFiber p).Nonempty := by
        by_contra h
        have h' : (steepFiber p).card = 0 := by simpa using h
        rw [h'] at h_half
        have hT_card : (F p hp_P).card = 0 := by linarith
        have hT_empty : F p hp_P = ∅ := Finset.card_eq_zero.mp hT_card
        have h_sset := hF_sset p hp_P
        rw [hT_empty] at h_sset
        have h_false : False := by
          simpa [Set.nonempty_iff_ne_empty] using h_sset.1
        exact h_false
      exact large_separated_subset_sset hδ_pos (by linarith) hC_in_pos
        (hF_sset p hp_P) h_steep_sub h_steep_sep h_steep_nonempty h_half
    have h8_v0 : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → (LemmaE.getDirV ℓ) 0 ≠ 0 := by
      intro p hp ℓ hℓ
      have hℓ' : ℓ ∈ steepFiber p := by simpa [F_oriented] using hℓ
      rcases hp with ⟨hp_P, _⟩
      have h_steep_cond : steep_cond ℓ := by
        have h_eq : steepFiber p = Finset.filter steep_cond (F p hp_P) := h_steepFiber_def p hp_P
        rw [h_eq] at hℓ'
        exact (Finset.mem_filter.mp hℓ').2
      exact (cp_steep_snap_flat ℓ h_steep_cond).1
    have h9_slope : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → |(affineLineSlopeIntercept ℓ).1| ≤ 1 := by
      intro p hp ℓ hℓ
      have hℓ' : ℓ ∈ steepFiber p := by simpa [F_oriented] using hℓ
      rcases hp with ⟨hp_P, _⟩
      have h_steep_cond : steep_cond ℓ := by
        have h_eq : steepFiber p = Finset.filter steep_cond (F p hp_P) := h_steepFiber_def p hp_P
        rw [h_eq] at hℓ'
        exact (Finset.mem_filter.mp hℓ').2
      exact (cp_steep_snap_flat ℓ h_steep_cond).2
    have h10_near : ∀ p hp, ∀ (ℓ : AffineLine), ℓ ∈ F_oriented p hp → p ∈ Metric.cthickening δ ℓ.1 := by
      intro p hp ℓ hℓ
      have hℓ' : ℓ ∈ steepFiber p := by simpa [F_oriented] using hℓ
      rcases hp with ⟨hp_P, _⟩
      have hℓ_in_F : ℓ ∈ F p hp_P := by
        have h_eq : steepFiber p = Finset.filter steep_cond (F p hp_P) := h_steepFiber_def p hp_P
        rw [h_eq] at hℓ'
        exact (Finset.mem_filter.mp hℓ').1
      exact hF_near p hp_P ℓ hℓ_in_F
    have h11_cslope : c_slope ≥ δ ^ ρ_slope := by
      simpa [c_slope] using hδ_slope
    have h12_mass : ncover δ P_oriented ≥ ENNReal.ofReal c_slope * ncover δ P := by
      have h5 : ncover δ P_oriented = ncover δ P' := by rfl
      rw [h5]
      have h6 : ncover δ P' ≥ ENNReal.ofReal c_slope * ncover δ P := by
        simpa [c_slope] using hP_steep_mass
      exact h6
    have h_cslope_eq : c_slope = 1 / 2 := by simp [c_slope]
    exact ⟨false, P', P_oriented, T_oriented, F_oriented, c_slope,
      h1_pos, h_cslope_eq, h2_sub, h3_false, h4_true, h5_ncover, h6_sub, h7_sset, h8_v0, h9_slope, h10_near, h11_cslope, h12_mass⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
