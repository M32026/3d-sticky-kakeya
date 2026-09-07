module

/-
  Base affine line parameterization utilities.

  Provides `getDirV`, `affineLineParams`, and `affineLineParams_correct`.
  Extracted from MainAppendixLemmaE to break import cycle with TubesAndSlopes.

  Dependencies: discretised_furstenberg_estimate
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace LemmaE

set_option autoImplicit true

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Pick a nonzero direction vector for an AffineLine. -/
noncomputable def getDirV (ℓ : AffineLine) : EuclideanPlane :=
  let dir := ℓ.1.direction
  have hfinrank : Module.finrank ℝ dir = 1 := ℓ.2
  have h_ne_bot : dir ≠ ⊥ := by
    have h1 : 1 ≤ Module.finrank ℝ dir := by rw [hfinrank] <;> norm_num
    have h2 : dir ≠ ⊥ := (Submodule.one_le_finrank_iff (S := dir)).mp h1
    exact h2
  Classical.choose ((Submodule.ne_bot_iff dir).mp h_ne_bot)

lemma getDirV_spec (ℓ : AffineLine) :
    getDirV ℓ ∈ ℓ.1.direction ∧ getDirV ℓ ≠ 0 := by
  let dir := ℓ.1.direction
  have hfinrank : Module.finrank ℝ dir = 1 := ℓ.2
  have h_ne_bot : dir ≠ ⊥ := by
    have h1 : 1 ≤ Module.finrank ℝ dir := by rw [hfinrank] <;> norm_num
    have h2 : dir ≠ ⊥ := (Submodule.one_le_finrank_iff (S := dir)).mp h1
    exact h2
  exact Classical.choose_spec ((Submodule.ne_bot_iff dir).mp h_ne_bot)

/-- Parameterize a non-horizontal AffineLine as (a,b) where x = a*y + b.
    If the direction vector has zero y-component, returns (0, off.0). -/
noncomputable def affineLineParams (ℓ : AffineLine) : ℝ × ℝ :=
  let off := ℓ.offset
  let v := getDirV ℓ
  let a := if v 1 = 0 then 0 else v 0 / v 1
  let b := off 0 - a * off 1
  (a, b)

/-- Correctness: if the chosen direction vector has nonzero y-component, then for
    every point q on the line, q 0 = a * q 1 + b. -/
lemma affineLineParams_correct (ℓ : AffineLine)
    (hv1_ne_zero : (getDirV ℓ) 1 ≠ 0) :
    ∀ (q : EuclideanPlane), q ∈ ℓ.1 →
      q 0 = (affineLineParams ℓ).1 * q 1 + (affineLineParams ℓ).2 := by
  let off := ℓ.offset
  let dir := ℓ.1.direction
  let v : EuclideanPlane := getDirV ℓ
  have hv_in_dir : v ∈ dir := (getDirV_spec ℓ).1
  have hv_ne_zero : v ≠ 0 := (getDirV_spec ℓ).2
  have hv1_ne_zero' : v 1 ≠ 0 := hv1_ne_zero
  have h_a : (affineLineParams ℓ).1 = v 0 / v 1 := by
    simp [affineLineParams, hv1_ne_zero'] <;> aesop
  have h_b : (affineLineParams ℓ).2 = off 0 - (v 0 / v 1) * off 1 := by
    simp [affineLineParams, hv1_ne_zero'] <;> aesop
  have h_main : ∀ (w : EuclideanPlane), w ∈ dir → ∃ (t : ℝ), w = t • v := by
    intro w hw
    let v' : dir := ⟨v, hv_in_dir⟩
    have hv'_ne_zero : v' ≠ 0 := by
      intro h
      have h' : (v' : EuclideanPlane) = 0 := by exact_mod_cast h
      exact hv_ne_zero h'
    have hfinrank : Module.finrank ℝ dir = 1 := ℓ.2
    have h_all : ∀ (w' : dir), ∃ (c : ℝ), c • v' = w' :=
      (finrank_eq_one_iff_of_nonzero' v' hv'_ne_zero).mp hfinrank
    let w' : dir := ⟨w, hw⟩
    rcases h_all w' with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h_eq : (c • v' : EuclideanPlane) = (w' : EuclideanPlane) := by
      exact congr_arg (fun (x : dir) => (x : EuclideanPlane)) hc
    have h_final : w = c • v := by
      simpa [v'] using Eq.symm h_eq
    exact h_final
  intro q hq
  have h_off_in : off ∈ ℓ.1 := ℓ.offset_mem
  have h_diff_in_dir : q - off ∈ dir :=
    AffineSubspace.vsub_mem_direction hq h_off_in
  rcases h_main (q - off) h_diff_in_dir with ⟨t, ht⟩
  have hq0 : q 0 = off 0 + t * v 0 := by
    have h : (q - off) 0 = t * v 0 := by rw [ht] <;> simp
    have h' : q 0 - off 0 = t * v 0 := h
    linarith
  have hq1 : q 1 = off 1 + t * v 1 := by
    have h : (q - off) 1 = t * v 1 := by rw [ht] <;> simp
    have h' : q 1 - off 1 = t * v 1 := h
    linarith
  rw [h_a, h_b, hq0, hq1]
  <;> field_simp [hv1_ne_zero'] <;> ring

/-- If two non-vertical affine lines have the same slope-intercept parameters,
    they are equal. -/
lemma affineLineParams_injective {ℓ₁ ℓ₂ : AffineLine}
    (hv₁ : (getDirV ℓ₁) 1 ≠ 0) (hv₂ : (getDirV ℓ₂) 1 ≠ 0)
    (h : affineLineParams ℓ₁ = affineLineParams ℓ₂) : ℓ₁ = ℓ₂ := by
  set a : ℝ := (affineLineParams ℓ₁).1 with ha_def
  set b : ℝ := (affineLineParams ℓ₁).2 with hb_def
  have h₂₁ : (affineLineParams ℓ₂).1 = a := by simp [ha_def, h]
  have h₂₂ : (affineLineParams ℓ₂).2 = b := by simp [hb_def, h]
  have h_char : ∀ (ℓ : AffineLine), (getDirV ℓ) 1 ≠ 0 →
      (affineLineParams ℓ).1 = a → (affineLineParams ℓ).2 = b →
        ∀ (q : EuclideanPlane), q ∈ ℓ.1 ↔ q 0 = a * q 1 + b := by
    intro ℓ hv ha hb q
    constructor
    · intro hqin
      have h_corr : q 0 = (affineLineParams ℓ).1 * q 1 + (affineLineParams ℓ).2 :=
        affineLineParams_correct ℓ hv q hqin
      rw [ha, hb] at h_corr
      exact h_corr
    · intro hq
      let off := ℓ.offset
      let v := getDirV ℓ
      have hoff : off ∈ ℓ.1 := ℓ.offset_mem
      have hv_in_dir : v ∈ ℓ.1.direction := (getDirV_spec ℓ).1
      have h_a_eq : (affineLineParams ℓ).1 = v 0 / v 1 := by
        have h_def : (affineLineParams ℓ).1 =
            if v 1 = 0 then (0 : ℝ) else v 0 / v 1 := by rfl
        rw [h_def, if_neg hv]
      have h_v0 : v 0 = a * v 1 := by
        have h9 : a = v 0 / v 1 := ha.symm.trans h_a_eq
        have h10 : (v 0 / v 1) * v 1 = v 0 := div_mul_cancel₀ (v 0) hv
        calc v 0
          = (v 0 / v 1) * v 1 := h10.symm
        _ = a * v 1 := by rw [h9]
      have h_off_eq : off 0 = a * off 1 + b := by
        have h_corr := affineLineParams_correct ℓ hv off hoff
        rw [ha, hb] at h_corr
        exact h_corr
      let w := q - off
      have hw0 : w 0 = a * w 1 := by
        dsimp only [w]
        have h : (q - off) 0 = q 0 - off 0 := by rfl
        have h' : (q - off) 1 = q 1 - off 1 := by rfl
        rw [h, h', hq, h_off_eq] <;> ring
      let t : ℝ := w 1 / v 1
      have h_t0 : (t • v) 0 = w 0 := by
        have h : (t • v) 0 = t * v 0 := by simp
        rw [h, h_v0]
        have ht : t = w 1 / v 1 := by rfl
        rw [ht]
        have h10 : (w 1 / v 1) * (a * v 1) = a * w 1 := by
          have h11 : (w 1 / v 1) * (a * v 1) = ((w 1 / v 1) * v 1) * a := by ring
          rw [h11]
          have h12 : (w 1 / v 1) * v 1 = w 1 := div_mul_cancel₀ (w 1) hv
          rw [h12] <;> ring
        rw [h10]
        exact hw0.symm
      have h_t1 : (t • v) 1 = w 1 := by
        have h : (t • v) 1 = t * v 1 := by simp
        rw [h]
        have ht : t = w 1 / v 1 := by rfl
        rw [ht]
        exact div_mul_cancel₀ (w 1) hv
      have h_tv : t • v = w := by
        ext i
        fin_cases i
        · exact h_t0
        · exact h_t1
      have h_w_dir : w ∈ ℓ.1.direction := by
        rw [← h_tv]
        exact ℓ.1.direction.smul_mem t hv_in_dir
      have h_q_eq : q = w +ᵥ off := by
        dsimp only [w]
        simp [vadd_eq_add] <;> abel
      rw [h_q_eq]
      exact AffineSubspace.vadd_mem_of_mem_direction h_w_dir hoff
  have h1 := h_char ℓ₁ hv₁ rfl rfl
  have h2 := h_char ℓ₂ hv₂ h₂₁ h₂₂
  have h_set : ∀ (x : EuclideanPlane), x ∈ ℓ₁.1 ↔ x ∈ ℓ₂.1 := by
    intro x
    rw [h1 x, h2 x]
  have h_sub : ℓ₁.1 = ℓ₂.1 := AffineSubspace.ext h_set
  exact Subtype.ext h_sub

end LemmaE
