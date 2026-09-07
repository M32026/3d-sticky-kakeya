/-
# Blow-Up Lemma — Half-Space Convergence at Reduced Boundary

Formalizes Maggi Theorem 15.5: at a reduced boundary point x, the blow-ups
`E_{x,r} = (E - x)/r` converge locally to the half-space `H_ν`.

## Main results

- `blowUp_perimeter_scaling`: perimeter scaling under blow-up
- `blowUp_compactness`: conditional compactness of blow-ups (depends on BV compactness)
- `blow_up_lemma`: main theorem — blow-ups converge to half-space

## Dependencies

- `ReducedBoundaryData`: analytic data at reduced boundary point
- `HalfSpaceCharacterization`: half-space identification (orientation + density)
- `BVCompactnessTranslation`: L¹_loc compactness (currently blocked)

## References

- Maggi, Sets of Finite Perimeter, Theorem 15.5
- Ambrosio-Fusco-Pallara, Functions of BV, Theorem 3.59
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LowerSemicontinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.SequenceCompactness
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.DirectionalVariationLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.HalfSpaceCharacterization
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- Half-space with normal ν through the origin: `{y | inner ℝ y ν < 0}`. -/
def halfSpace (ν : E n) : Set (E n) := {y | inner ℝ y ν < 0}

/-- Blow-up excess: L¹ distance between blow-up and half-space on ball 0 R. -/
noncomputable def blowUpExcess (U : Set (E n)) (x : E n) (ν : E n) (r R : ℝ) : ENNReal :=
  volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R)

-- ============================================================================
-- Step 1: Perimeter scaling under blow-up
-- ============================================================================

/-- The blow-up `E_{x,r} = (E - x)/r` equals scaling by `1/r` after translation. -/
lemma blowUp_eq_scale_translate {S : Set (E n)} {x : E n} {r : ℝ} (hr : 0 < r) :
    blowUp S x r = Geometry.Perimeter.scaleSet (1 / r) ((fun y => y - x) '' S) := by
  ext z
  simp only [blowUp, blowUpMap, Geometry.Perimeter.scaleSet, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - x, ⟨y, hy, by simp⟩, ?_⟩
    simp [smul_smul, hr.ne'] <;> ring
  · rintro ⟨z', ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp [smul_smul, hr.ne'] <;> ring

/-- Global perimeter scaling under blow-up.

`P(E_{x,r}) = r^{1-n} · P(E)` for `r > 0`. -/
theorem blowUp_perimeter_scaling {S : Set (E n)} (hS : MeasurableSet S)
    {x : E n} {r : ℝ} (hr : 0 < r) (hn : 1 ≤ n) :
    Geometry.Perimeter.perimeter (blowUp S x r) =
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * Geometry.Perimeter.perimeter S := by
  have hne : (1 / r : ℝ) ≠ 0 := by positivity
  have h_trans : Geometry.Perimeter.perimeter ((fun y : E n => y - x) '' S) =
      Geometry.Perimeter.perimeter S := by
    have h1 : (fun y : E n => y - x) '' S = Geometry.Perimeter.translateSet S (-x) := by
      ext z
      simp only [Geometry.Perimeter.translateSet, Set.mem_image]
      <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, by abel⟩
    rw [h1]
    exact Geometry.Perimeter.perimeter_translation S hS (-x)
  have h_main : Geometry.Perimeter.perimeter (Geometry.Perimeter.scaleSet (1 / r) ((fun y : E n => y - x) '' S)) =
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * Geometry.Perimeter.perimeter ((fun y : E n => y - x) '' S) :=
    Geometry.Perimeter.perimeter_scaling ((fun y : E n => y - x) '' S)
      (by
        let g : E n → E n := fun z => z + x
        have hg : Measurable g := measurable_id.add measurable_const
        have h_eq : (fun y : E n => y - x) '' S = g ⁻¹' S := by
          ext z
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩; simpa [g] using hy
          · intro hz; refine ⟨z + x, hz, by simp [g] <;> abel⟩
        rw [h_eq]
        exact hg hS)
      (by positivity) hn
  rw [blowUp_eq_scale_translate hr, h_main, h_trans]

-- ============================================================================
-- Step 2: Compactness (depends on BV compactness translation)
-- ============================================================================

/-- **Conditional compactness of blow-ups**.

If the blow-ups have uniformly bounded volume and translation continuity
on compact sets, then every sequence `r_k → 0` has a subsequence converging
in L¹_loc to some measurable set `F`. -/
theorem blowUp_compactness {S : Set (E n)} (hS : MeasurableSet S)
    (x : E n)
    (h_vol_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ (r : ℝ), 0 < r → r < 1 →
        volume (blowUp S x r ∩ K) ≤ C)
    (h_trans_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → r < 1 → ∀ (h : E n),
        volume (symmDiff (blowUp S x r) ((fun y => y + h) '' (blowUp S x r)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖)) :
    ∀ (r_seq : ℕ → ℝ), (∀ k, 0 < r_seq k) → Tendsto r_seq atTop (nhds 0) →
      ∃ (F : Set (E n)) (subseq : ℕ → ℕ), StrictMono subseq ∧
        MeasurableSet F ∧
        ∀ (K : Set (E n)), IsCompact K →
          Tendsto (fun k => volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K))
            atTop (nhds 0) := by
  intro r_seq hr_pos hr_tendsto
  have h1 : ∀ᶠ k in atTop, r_seq k < 1 := hr_tendsto (Iio_mem_nhds (by norm_num))
  rcases Filter.eventually_atTop.mp h1 with ⟨N, hN⟩
  let E_seq : ℕ → Set (E n) := fun k => blowUp S x (r_seq (k + N))
  have h_meas_blowUp : ∀ (r : ℝ), 0 < r → MeasurableSet (blowUp S x r) := by
    intro r hr
    let h : E n ≃ᵐ E n :=
      { toFun := blowUpMap x r
        invFun := fun z => r • z + x
        left_inv := fun y => by simp [blowUpMap, smul_smul, hr.ne'] <;> abel
        right_inv := fun z => by simp [blowUpMap, smul_smul, hr.ne'] <;> abel
        measurable_toFun := by
          have hc : Continuous (blowUpMap x r) := by
            change Continuous (fun y : E n => (1 / r) • (y - x))
            fun_prop
          exact hc.measurable
        measurable_invFun := by
          have hc : Continuous (fun z : E n => r • z + x) := by
            fun_prop
          exact hc.measurable }
    exact h.measurableSet_image.mpr hS
  have h_meas_seq : ∀ k, MeasurableSet (E_seq k) := by
    intro k
    exact h_meas_blowUp (r_seq (k + N)) (hr_pos (k + N))
  have h_vol_seq : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K) ≤ C := by
    intro K hK
    rcases h_vol_bound K hK with ⟨C, hC⟩
    refine ⟨C, fun k => hC (r_seq (k + N)) (hr_pos (k + N)) (hN (k + N) (by linarith))⟩
  have h_trans_seq : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ k, ∀ (h : E n),
        volume (Geometry.symmDiff (E_seq k) ((fun y => y + h) '' (E_seq k)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) := by
    intro K hK
    rcases h_trans_bound K hK with ⟨C, hC⟩
    refine ⟨C, fun k h => ?_⟩
    have h_orig := hC (r_seq (k + N)) (hr_pos (k + N)) (hN (k + N) (by linarith)) h
    have h_E : E_seq k = blowUp S x (r_seq (k + N)) := by rfl
    have h_goal : Geometry.symmDiff (E_seq k) ((fun y : E n => y + h) '' E_seq k) ∩ K =
        symmDiff (blowUp S x (r_seq (k + N))) ((fun y : E n => y + h) '' (blowUp S x (r_seq (k + N)))) ∩ K := by
      rw [h_E] <;> rfl
    rw [h_goal]
    exact h_orig
  rcases bv_compactness_sequence_of_translation h_meas_seq h_vol_seq h_trans_seq with
    ⟨F, subseq', hsub_strict, hF_meas, h_conv⟩
  let subseq : ℕ → ℕ := fun k => subseq' k + N
  have hsub_strict' : StrictMono subseq := by
    intro a b hab
    have h : subseq' a < subseq' b := hsub_strict hab
    dsimp only [subseq]
    exact add_lt_add_left h N
  refine ⟨F, subseq, hsub_strict', hF_meas, ?_⟩
  intro K hK
  have h_final := h_conv K hK
  have h_func : (fun k : ℕ => volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K)) =
      (fun k : ℕ => volume (Geometry.symmDiff (E_seq (subseq' k)) F ∩ K)) := by
    funext k
    have h1 : E_seq (subseq' k) = blowUp S x (r_seq (subseq k)) := by
      simp [E_seq, subseq] <;> rfl
    have h2 : Geometry.symmDiff (E_seq (subseq' k)) F = symmDiff (blowUp S x (r_seq (subseq k))) F := by
      rw [h1] <;> rfl
    rw [h2]
  rwa [h_func]

-- ============================================================================
-- Subsequence principle
-- ============================================================================

/-- **Subsequence principle for convergence along `nhdsWithin 0 (Ioi 0)`**.

If every positive sequence `r_k → 0` has a subsequence along which `f(r_k) → l`,
then `f(r) → l` as `r → 0⁺`. -/
lemma tendsto_of_subsequence_principle {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} {l : X} (h : ∀ (r_seq : ℕ → ℝ),
      (∀ k, 0 < r_seq k) → Tendsto r_seq atTop (nhds 0) →
      ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
        Tendsto (f ∘ (r_seq ∘ subseq)) atTop (nhds l)) :
    Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds l) := by
  have h_main : ∀ (ns : ℕ → ℝ), Tendsto ns atTop (nhdsWithin 0 (Set.Ioi 0)) →
      ∃ (ms : ℕ → ℕ), Tendsto (f ∘ (ns ∘ ms)) atTop (nhds l) := by
    intro ns hns
    have h1 : ∀ᶠ (k : ℕ) in Filter.atTop, 0 < ns k := by
      have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := self_mem_nhdsWithin
      exact hns h2
    rcases Filter.eventually_atTop.mp h1 with ⟨N, hN⟩
    let r_seq : ℕ → ℝ := fun k => ns (k + N)
    have hr_pos : ∀ k, 0 < r_seq k := by intro k; exact hN (k + N) (by linarith)
    have hr_tendsto : Tendsto r_seq atTop (nhds 0) := by
      have h3 : Tendsto ns atTop (nhds 0) := hns.mono_right nhdsWithin_le_nhds
      exact h3.comp (tendsto_add_atTop_nat N)
    rcases h r_seq hr_pos hr_tendsto with ⟨subseq, hsub_mono, hconv⟩
    let ms : ℕ → ℕ := fun k => subseq k + N
    have hms_mono : StrictMono ms := by
      intro i j h; simp [ms, hsub_mono h] <;> linarith
    have h4 : f ∘ (ns ∘ ms) = f ∘ (r_seq ∘ subseq) := by
      funext k; rfl
    rw [h4] at *
    exact ⟨ms, hconv⟩
  exact Filter.tendsto_of_subseq_tendsto h_main

-- ============================================================================
-- Symmetric difference bound
-- ============================================================================

/-- **Bound for symmetric difference with half-space vs. limit set**.

If `F =ᵐ[volume] Hν`, then for any `A` and `R > 0`,
`volume(symmDiff A Hν ∩ ball 0 R) ≤ volume(symmDiff A F ∩ closedBall 0 R)`. -/
lemma symmDiff_halfspace_bound {A F Hν : Set (E n)} {R : ℝ} (hR : 0 < R)
    (h : F =ᵐ[volume] Hν) :
    volume (symmDiff A Hν ∩ ball (0 : E n) R) ≤
    volume (symmDiff A F ∩ closedBall (0 : E n) R) := by
  have h1 : ∀ᵐ (x : E n) ∂volume, x ∉ (F \ Hν) := by
    filter_upwards [h] with x hx
    intro hxFHν
    have h4 : x ∈ F := hxFHν.1
    have h5 : x ∉ Hν := hxFHν.2
    have hx' : (x ∈ F) ↔ (x ∈ Hν) := Iff.of_eq hx
    exact h5 (hx'.mp h4)
  have h2 : ∀ᵐ (x : E n) ∂volume, x ∉ (Hν \ F) := by
    filter_upwards [h] with x hx
    intro hxHνF
    have h4 : x ∈ Hν := hxHνF.1
    have h5 : x ∉ F := hxHνF.2
    have hx' : (x ∈ F) ↔ (x ∈ Hν) := Iff.of_eq hx
    exact h5 (hx'.mpr h4)
  have h_null1 : volume (F \ Hν) = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr h1
  have h_null2 : volume (Hν \ F) = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr h2
  have h_null : volume (symmDiff F Hν) = 0 := by
    have h3 : volume (symmDiff F Hν) ≤ volume (F \ Hν) + volume (Hν \ F) := measure_union_le _ _
    rw [h_null1, h_null2] at h3
    simpa using h3
  have h_subset : symmDiff A Hν ∩ ball (0 : E n) R ⊆
      symmDiff A F ∩ closedBall (0 : E n) R ∪ symmDiff F Hν := by
    intro x hx
    have hx_ball : x ∈ ball (0 : E n) R := hx.2
    have hx_closed : x ∈ closedBall (0 : E n) R := ball_subset_closedBall hx_ball
    have hx_diff : x ∈ symmDiff A Hν := hx.1
    rcases hx_diff with (h1 | h2)
    · -- x ∈ A \ Hν
      by_cases h3 : x ∈ F
      · right; exact Or.inl ⟨h3, h1.2⟩
      · left; exact ⟨Or.inl ⟨h1.1, h3⟩, hx_closed⟩
    · -- x ∈ Hν \ A
      by_cases h3 : x ∈ F
      · left; exact ⟨Or.inr ⟨h3, h2.2⟩, hx_closed⟩
      · right; exact Or.inr ⟨h2.1, h3⟩
  calc
    volume (symmDiff A Hν ∩ ball (0 : E n) R)
      ≤ volume (symmDiff A F ∩ closedBall (0 : E n) R ∪ symmDiff F Hν) :=
        measure_mono h_subset
    _ ≤ volume (symmDiff A F ∩ closedBall (0 : E n) R) + volume (symmDiff F Hν) :=
        measure_union_le _ _
    _ = volume (symmDiff A F ∩ closedBall (0 : E n) R) + 0 := by rw [h_null]
    _ = volume (symmDiff A F ∩ closedBall (0 : E n) R) := by simp

-- ============================================================================
-- Main theorem (assembly)
-- ============================================================================

/-- **Blow-up lemma** (Maggi Theorem 15.5).

At a reduced boundary point `x` with normal `ν`, the blow-ups `E_{x,r}`
converge locally to the half-space `H_ν = {y : inner(y,ν) < 0}`.

Proof:
1. `ReducedBoundaryData` gives uniform volume/translation bounds and half-space identification
2. BV compactness extracts L¹_loc-convergent subsequence
3. `reduced_boundary_blowup_data` identifies the limit as Hν
4. Subsequence principle upgrades to full family convergence -/
theorem blow_up_lemma {S : Set (E n)} (hS : MeasurableSet S)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1)
    (hdata : ReducedBoundaryData S x ν)
    (hn : 2 ≤ n) :
    ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ => blowUpExcess S x ν r R)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  dsimp only [blowUpExcess, halfSpace]
  intro R hR
  let Hν : Set (E n) := {y | inner ℝ y ν < 0}
  have hHν_meas : MeasurableSet Hν := by
    apply IsOpen.measurableSet
    exact isOpen_lt (continuous_id.inner continuous_const) continuous_const
  rcases reduced_boundary_blowup_data hS x ν hν_unit hdata
    with ⟨h_vol_bound, h_trans_bound, h_limit_halfspace⟩
  apply tendsto_of_subsequence_principle
  intro r_seq hr_pos hr_tendsto
  rcases blowUp_compactness hS x h_vol_bound h_trans_bound r_seq hr_pos hr_tendsto
    with ⟨F, subseq, hsub_strict, hF_meas, h_conv⟩
  have hF_halfspace : F =ᵐ[volume] Hν :=
    h_limit_halfspace F hF_meas (r_seq ∘ subseq)
      (fun k => hr_pos (subseq k))
      (hr_tendsto.comp hsub_strict.tendsto_atTop)
      h_conv
  refine ⟨subseq, hsub_strict, ?_⟩
  let K_cmp : Set (E n) := closedBall (0 : E n) R
  have hK_compact : IsCompact K_cmp := isCompact_closedBall _ _
  have h_conv_K : Tendsto (fun k : ℕ =>
      volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K_cmp))
      atTop (nhds 0) := h_conv K_cmp hK_compact
  have h_bound : ∀ k : ℕ,
      volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R) ≤
      volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K_cmp) := by
    intro k
    exact symmDiff_halfspace_bound hR hF_halfspace
  have h_zero : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
  have h_ev1 : ∀ᶠ k in atTop, (0 : ENNReal) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R) := by
    have h_set : {k : ℕ | (0 : ENNReal) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R)} = Set.univ := by
      ext k; simp
    change {k : ℕ | (0 : ENNReal) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R)} ∈ atTop
    rw [h_set]
    exact Filter.univ_mem
  have h_ev2 : ∀ᶠ k in atTop, volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K_cmp) := by
    have h_set : {k : ℕ | volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K_cmp)} = Set.univ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact h_bound k
    change {k : ℕ | volume (symmDiff (blowUp S x (r_seq (subseq k))) Hν ∩ ball (0 : E n) R) ≤ volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K_cmp)} ∈ atTop
    rw [h_set]
    exact Filter.univ_mem
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_conv_K h_ev1 h_ev2

end Geometry.StructureTheorem
