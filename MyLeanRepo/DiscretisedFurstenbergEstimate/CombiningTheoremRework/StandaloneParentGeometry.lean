module

/-
  Standalone parent geometry + covering doubling chain.

  Resolves the geometry mismatch between root (standalone) DyadicTube.toSet
  (parameter rectangle union of lines) and project DyadicTube.toSet (strip).

  Route:
  1. Root containment C.toSet ⊆ U.toSet → |Δslope|, |Δintercept| ≤ δ_m - δ_n
  2. Covering cell relation → paramDistLinf(T, shifted U) ≤ 2δ_m
  3. 5-Lipschitz parameter→AffineLine → dist ≤ 10δ_m
  4. Coarse lines form 12δ_m-cover → Ncover(12δ_m) ≤ |coarseTubes|
  5. Two factor-2 doublings → Ncover(3δ_m) ≤ 262144² * |coarseTubes|

  Whiteprint node: coarse_elimination / standalone_parent_geometry
  Dependencies: CoarseNcoverToCard, AffineLineDoubling, InductionOnScales.Basic
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineDoubling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseParentSSetRatio
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CoveringUtils

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.Section6
open DyadicCardToNcover (toAffineLine lineOfSlopeIntercept)

/-- The two dyadicDelta definitions are equal. -/
lemma _root_.dyadicDelta_eq_main (n : ℕ) :
    _root_.dyadicDelta n = DiscretisedFurstenbergEstimate.dyadicDelta n := by
  simp [_root_.dyadicDelta, DiscretisedFurstenbergEstimate.dyadicDelta]

/-! ========================================================================
   Root containment → parameter distance bounds
   ======================================================================== -/

/-- Root rectangle containment implies slope difference ≤ δ_m - δ_n. -/
lemma root_containment_slope_bound
    {n m : ℕ} (hnm : m ≤ n)
    (C : _root_.DyadicTube n) (U : _root_.DyadicTube m)
    (h_contain : C.toSet ⊆ U.toSet) :
    |C.slope - U.slope| ≤ _root_.dyadicDelta m - _root_.dyadicDelta n := by
  set δ_n := _root_.dyadicDelta n with hδn
  set δ_m := _root_.dyadicDelta m with hδm
  set f : ℕ := coarseRefinementFactor n m with hf
  have hf_pos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hδn_pos : 0 < δ_n := by simp [hδn, _root_.dyadicDelta] <;> positivity
  have hδm_pos : 0 < δ_m := by simp [hδm, _root_.dyadicDelta] <;> positivity
  have h_rel : δ_n = δ_m / (f : ℝ) := by
    simp only [hδn, hδm, hf, _root_.dyadicDelta, coarseRefinementFactor]
    have h₁ : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
      simp [Nat.cast_sub hnm] <;> ring
    rw [h₁]
    simp [Real.rpow_add] <;> field_simp <;> ring
  have h := (InductionOnScales.tube_containment_iff hnm C U).mp h_contain
  have h1 : (U.a : ℝ) * δ_m ≤ (C.a : ℝ) * δ_n := by
    have h1a : (U.a : ℤ) * (f : ℤ) ≤ C.a := h.1
    have h1b : (U.a : ℝ) * (f : ℝ) ≤ (C.a : ℝ) := by exact_mod_cast h1a
    calc (U.a : ℝ) * δ_m
      = ((U.a : ℝ) * (f : ℝ)) * (δ_m / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
    _ ≤ (C.a : ℝ) * (δ_m / (f : ℝ)) := by gcongr
    _ = (C.a : ℝ) * δ_n := by rw [←h_rel]
  have h2 : (C.a + 1 : ℝ) * δ_n ≤ (U.a + 1 : ℝ) * δ_m := by
    have h2a : C.a + 1 ≤ (U.a + 1) * (f : ℤ) := h.2.1
    have h2b : (C.a + 1 : ℝ) ≤ (U.a + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h2a
    calc (C.a + 1 : ℝ) * δ_n
      = (C.a + 1 : ℝ) * (δ_m / (f : ℝ)) := by rw [←h_rel]
    _ ≤ ((U.a + 1 : ℝ) * (f : ℝ)) * (δ_m / (f : ℝ)) := by gcongr
    _ = (U.a + 1 : ℝ) * δ_m := by field_simp [hf_pos.ne'] <;> ring
  have h3 : 0 ≤ C.slope - U.slope := by
    simpa [_root_.DyadicTube.slope] using h1
  have h4 : C.slope - U.slope ≤ δ_m - δ_n := by
    simpa [_root_.DyadicTube.slope] using by linarith
  rw [abs_of_nonneg h3] <;> linarith

/-- Root rectangle containment implies intercept difference ≤ δ_m - δ_n. -/
lemma root_containment_intercept_bound
    {n m : ℕ} (hnm : m ≤ n)
    (C : _root_.DyadicTube n) (U : _root_.DyadicTube m)
    (h_contain : C.toSet ⊆ U.toSet) :
    |C.intercept - U.intercept| ≤ _root_.dyadicDelta m - _root_.dyadicDelta n := by
  set δ_n := _root_.dyadicDelta n with hδn
  set δ_m := _root_.dyadicDelta m with hδm
  set f : ℕ := coarseRefinementFactor n m with hf
  have hf_pos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hδn_pos : 0 < δ_n := by simp [hδn, _root_.dyadicDelta] <;> positivity
  have hδm_pos : 0 < δ_m := by simp [hδm, _root_.dyadicDelta] <;> positivity
  have h_rel : δ_n = δ_m / (f : ℝ) := by
    simp only [hδn, hδm, hf, _root_.dyadicDelta, coarseRefinementFactor]
    have h₁ : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
      simp [Nat.cast_sub hnm] <;> ring
    rw [h₁]
    simp [Real.rpow_add] <;> field_simp <;> ring
  have h := (InductionOnScales.tube_containment_iff hnm C U).mp h_contain
  have h1 : (U.b : ℝ) * δ_m ≤ (C.b : ℝ) * δ_n := by
    have h1a : (U.b : ℤ) * (f : ℤ) ≤ C.b := h.2.2.1
    have h1b : (U.b : ℝ) * (f : ℝ) ≤ (C.b : ℝ) := by exact_mod_cast h1a
    calc (U.b : ℝ) * δ_m
      = ((U.b : ℝ) * (f : ℝ)) * (δ_m / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
    _ ≤ (C.b : ℝ) * (δ_m / (f : ℝ)) := by gcongr
    _ = (C.b : ℝ) * δ_n := by rw [←h_rel]
  have h2 : (C.b + 1 : ℝ) * δ_n ≤ (U.b + 1 : ℝ) * δ_m := by
    have h2a : C.b + 1 ≤ (U.b + 1) * (f : ℤ) := h.2.2.2
    have h2b : (C.b + 1 : ℝ) ≤ (U.b + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h2a
    calc (C.b + 1 : ℝ) * δ_n
      = (C.b + 1 : ℝ) * (δ_m / (f : ℝ)) := by rw [←h_rel]
    _ ≤ ((U.b + 1 : ℝ) * (f : ℝ)) * (δ_m / (f : ℝ)) := by gcongr
    _ = (U.b + 1 : ℝ) * δ_m := by field_simp [hf_pos.ne'] <;> ring
  have h3 : 0 ≤ C.intercept - U.intercept := by
    simpa [_root_.DyadicTube.intercept] using h1
  have h4 : C.intercept - U.intercept ≤ δ_m - δ_n := by
    simpa [_root_.DyadicTube.intercept] using by linarith
  rw [abs_of_nonneg h3] <;> linarith

/-! ========================================================================
   Root containment → AffineLine distance bound
   ======================================================================== -/

/-- Given root containment C.toSet ⊆ U_stand.toSet, covering cell relation
    (C.a = T.a, |C.b - T.b| ≤ 1), and slope/intercept bounds, the AffineLine
    distance between T and tubeToMainShifted(U_stand) is ≤ 10*δ_m. -/
lemma root_containment_to_affine_dist
    {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m)
    (hC_slope : C.a = T.a)
    (hC_intercept : |(C.b : ℝ) - (T.b : ℝ)| ≤ 1)
    (h_contain : C.toSet ⊆ U_stand.toSet)
    (h_T_slope : |T.slope| ≤ 1)
    (h_T_intercept : |T.intercept| ≤ 3)
    (h_U_slope : |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1) :
    dist (toAffineLine T) (toAffineLine (Bridge.tubeToMainShifted U_stand)) ≤
      10 * dyadicDelta m := by
  set δ_n := dyadicDelta n with hδn
  set δ_m := dyadicDelta m with hδm
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m
  let U_main := Bridge.tubeToMainShifted U_stand
  have hδn_eq : _root_.dyadicDelta n = δ_n := _root_.dyadicDelta_eq_main n
  have hδm_eq : _root_.dyadicDelta m = δ_m := _root_.dyadicDelta_eq_main m

  -- C.slope = T.slope
  have h_C_slope_eq : C.slope = T.slope := by
    have hca : (C.a : ℝ) = (T.a : ℝ) := by exact_mod_cast hC_slope
    have h : C.slope = (C.a : ℝ) * _root_.dyadicDelta n := by rfl
    have h2 : T.slope = (T.a : ℝ) * δ_n := by rfl
    rw [h, h2, hca, hδn_eq]

  -- Parameter bounds from root containment
  have h_slope_bound : |C.slope - U_stand.slope| ≤ δ_m - δ_n := by
    have h := root_containment_slope_bound hnm C U_stand h_contain
    rw [hδm_eq, hδn_eq] at h
    exact h
  have h_intercept_bound : |C.intercept - U_stand.intercept| ≤ δ_m - δ_n := by
    have h := root_containment_intercept_bound hnm C U_stand h_contain
    rw [hδm_eq, hδn_eq] at h
    exact h

  -- |T.intercept - C.intercept| ≤ δ_n
  have h_TC_intercept : |T.intercept - C.intercept| ≤ δ_n := by
    have h_eq1 : T.intercept = (T.b : ℝ) * δ_n := by rfl
    have h_eq2 : C.intercept = (C.b : ℝ) * _root_.dyadicDelta n := by rfl
    rw [h_eq1, h_eq2, hδn_eq]
    have h_distrib : (T.b : ℝ) * δ_n - (C.b : ℝ) * δ_n = ((T.b : ℝ) - (C.b : ℝ)) * δ_n := by ring
    rw [h_distrib, abs_mul, abs_of_pos hδn_pos]
    have h2 : |(T.b : ℝ) - (C.b : ℝ)| ≤ 1 := by
      have h3 : |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 := hC_intercept
      have h4 : |(T.b : ℝ) - (C.b : ℝ)| = |(C.b : ℝ) - (T.b : ℝ)| := by
        have h5 : (T.b : ℝ) - (C.b : ℝ) = -((C.b : ℝ) - (T.b : ℝ)) := by ring
        rw [h5, abs_neg]
      rw [h4]; exact h3
    nlinarith

  -- U_main.slope = U_stand.slope
  have h_U_main_a : U_main.a = U_stand.a := by
    simp [U_main, Bridge.tubeToMainShifted] <;> rfl
  have h_U_main_slope : U_main.slope = U_stand.slope := by
    have h1 : U_main.slope = (U_main.a : ℝ) * δ_m := by rfl
    have h2 : U_stand.slope = (U_stand.a : ℝ) * _root_.dyadicDelta m := by rfl
    rw [h1, h2, h_U_main_a, hδm_eq] <;> ring

  -- U_main.intercept = U_stand.intercept + δ_m
  have h_U_main_b : U_main.b = U_stand.b + 1 := by
    simp [U_main, Bridge.tubeToMainShifted] <;> rfl
  have h_U_main_intercept : U_main.intercept = U_stand.intercept + δ_m := by
    have h1 : U_main.intercept = (U_main.b : ℝ) * δ_m := by rfl
    have h2 : U_stand.intercept = (U_stand.b : ℝ) * _root_.dyadicDelta m := by rfl
    rw [h1, h2, h_U_main_b, hδm_eq] <;> simp [Nat.cast_add] <;> ring

  -- |U_main.slope - T.slope| ≤ 2*δ_m
  have h_abs_comm1 : |U_stand.slope - C.slope| = |C.slope - U_stand.slope| := by
    have h5 : U_stand.slope - C.slope = -(C.slope - U_stand.slope) := by ring
    rw [h5, abs_neg]
  have h_diff_slope : |U_main.slope - T.slope| ≤ 2 * δ_m := by
    calc |U_main.slope - T.slope|
      = |U_stand.slope - C.slope| := by rw [h_U_main_slope, h_C_slope_eq] <;> ring
    _ = |C.slope - U_stand.slope| := h_abs_comm1
    _ ≤ δ_m - δ_n := h_slope_bound
    _ ≤ δ_m := by linarith [hδn_pos]
    _ ≤ 2 * δ_m := by linarith

  -- |U_main.intercept - T.intercept| ≤ 2*δ_m
  have h_abs2 : |U_stand.intercept - C.intercept| = |C.intercept - U_stand.intercept| := by
    have h5 : U_stand.intercept - C.intercept = -(C.intercept - U_stand.intercept) := by ring
    rw [h5, abs_neg]
  have h_abs3 : |T.intercept - C.intercept| = |C.intercept - T.intercept| := by
    have h5 : T.intercept - C.intercept = -(C.intercept - T.intercept) := by ring
    rw [h5, abs_neg]
  have h_diff_intercept : |U_main.intercept - T.intercept| ≤ 2 * δ_m := by
    have h_expr : U_main.intercept - T.intercept =
        (U_stand.intercept - C.intercept) + (C.intercept - T.intercept) + δ_m := by
      rw [h_U_main_intercept] <;> ring
    rw [h_expr]
    set a := U_stand.intercept - C.intercept with ha_def
    set b := C.intercept - T.intercept with hb_def
    have h6 : |a + b| ≤ |a| + |b| := by
      exact AbsoluteValue.add_le AbsoluteValue.abs a b
    have h7 : |a + b + δ_m| ≤ |a + b| + δ_m := by
      have h8 : |a + b + δ_m| ≤ |a + b| + |δ_m| := by
        exact AbsoluteValue.add_le AbsoluteValue.abs (a + b) δ_m
      rw [abs_of_pos hδm_pos] at h8
      exact h8
    have h_tri : |a + b + δ_m| ≤ |a| + |b| + δ_m := by linarith
    have h_abs2' : |a| = |C.intercept - U_stand.intercept| := by
      simpa [ha_def] using h_abs2
    have h_abs3' : |b| = |T.intercept - C.intercept| := by
      simpa [hb_def] using h_abs3.symm
    rw [h_abs2', h_abs3'] at h_tri
    linarith [h_intercept_bound, h_TC_intercept]

  -- max bound
  have h_max : max |U_main.slope - T.slope| |U_main.intercept - T.intercept| ≤ 2 * δ_m :=
    max_le h_diff_slope h_diff_intercept

  -- Apply forward Lipschitz: U_main as first, T as second (uses h_T_intercept)
  have h_lip : dist (toAffineLine U_main) (toAffineLine T) ≤
      5 * max |U_main.slope - T.slope| |U_main.intercept - T.intercept| :=
    affine_line_forward_lipschitz h_U_slope h_T_slope h_T_intercept

  have h_symm : dist (toAffineLine T) (toAffineLine U_main) =
      dist (toAffineLine U_main) (toAffineLine T) := dist_comm _ _

  rw [h_symm]
  calc dist (toAffineLine U_main) (toAffineLine T)
    ≤ 5 * max |U_main.slope - T.slope| |U_main.intercept - T.intercept| := h_lip
  _ ≤ 5 * (2 * δ_m) := by gcongr
  _ = 10 * δ_m := by ring

/-! ========================================================================
   Ncover(12δ_m) ≤ |coarseTubes| via root containment
   ======================================================================== -/

/-- Given fine tubes each with a root-contained coarse parent, the coarse
    affine lines form a 12δ_m-cover of the fine affine lines. -/
lemma coarse_ncover_12_le_coarseCard_root
    {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (h_slope_bound : ∀ T ∈ fineTubes, |T.slope| ≤ 1)
    (h_intercept_bound : ∀ T ∈ fineTubes, |T.intercept| ≤ 3)
    (h_parent : ∀ T ∈ fineTubes,
      ∃ (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m),
        C.a = T.a ∧
        |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 ∧
        C.toSet ⊆ U_stand.toSet ∧
        |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1 ∧
        Bridge.tubeToMainShifted U_stand ∈ coarseTubes) :
    Ncover (12 * dyadicDelta m)
      (toAffineLine '' (fineTubes : Set (DyadicTube n))) ≤
      (coarseTubes.card : ENNReal) := by
  classical
  set δ_m := dyadicDelta m with hδm
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m
  set allLines := toAffineLine '' (fineTubes : Set (DyadicTube n)) with hallLines
  set coarseLines := toAffineLine '' (coarseTubes : Set (DyadicTube m)) with hcoarseLines

  have h_cover : Metric.IsCover (12 * δ_m).toNNReal allLines coarseLines := by
    intro ℓ hℓ
    have h_exists : ∃ (T : DyadicTube n), T ∈ fineTubes ∧ toAffineLine T = ℓ := by
      simpa [allLines, Set.mem_image] using hℓ
    rcases h_exists with ⟨T, hT, rfl⟩
    rcases h_parent T hT with ⟨C, U_stand, hC_slope, hC_intercept, h_contain, h_U_slope, hU_shifted_in⟩
    let U_main := Bridge.tubeToMainShifted U_stand
    have hU_in_coarse : U_main ∈ coarseTubes := hU_shifted_in
    have h_dist : dist (toAffineLine T) (toAffineLine U_main) ≤ 10 * δ_m :=
      root_containment_to_affine_dist hnm T C U_stand hC_slope hC_intercept h_contain
        (h_slope_bound T hT) (h_intercept_bound T hT) h_U_slope
    have h_dist' : dist (toAffineLine T) (toAffineLine U_main) ≤ 12 * δ_m := by
      linarith [hδm_pos]
    refine ⟨toAffineLine U_main, ?_, ?_⟩
    · exact ⟨U_main, hU_in_coarse, rfl⟩
    · have h_edist : edist (toAffineLine T) (toAffineLine U_main) ≤ ↑(12 * δ_m).toNNReal := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal h_dist'
      exact h_edist

  set ncover_nat : ℕ∞ := Metric.externalCoveringNumber (12 * δ_m).toNNReal allLines with hdef
  have h_main : ncover_nat ≤ coarseLines.encard :=
    h_cover.externalCoveringNumber_le_encard
  have h_coarseLines_encard : coarseLines.encard ≤ (coarseTubes.card : ENat) := by
    calc coarseLines.encard
      = (toAffineLine '' (coarseTubes : Set (DyadicTube m))).encard := by rfl
    _ ≤ (coarseTubes : Set (DyadicTube m)).encard := Set.encard_image_le _ _
    _ = (coarseTubes.card : ENat) := by simp
  have h_final_nat : ncover_nat ≤ (coarseTubes.card : ENat) :=
    le_trans h_main h_coarseLines_encard
  have h_final : (ncover_nat : ENNReal) ≤ (coarseTubes.card : ENNReal) := by
    exact_mod_cast h_final_nat
  simpa [Ncover, hdef] using h_final

/-! ========================================================================
   Doubling chain: Ncover(3δ_m) ≤ D² * Ncover(12δ_m)
   ======================================================================== -/

/-- Two factor-2 doublings: Ncover(3δ_m) ≤ 262144² * Ncover(12δ_m),
    for sets of affine lines with bounded slope/intercept. -/
lemma ncover_3_le_doubling_sq_of_12
    {m : ℕ}
    (E : Set _)
    (hE : ∀ ℓ ∈ E, ∃ (slope intercept : ℝ), |slope| ≤ 1 ∧ |intercept| ≤ 3 ∧
      lineOfSlopeIntercept slope intercept = ℓ) :
    Ncover (3 * dyadicDelta m) E ≤
      (262144 : ENNReal)^2 * Ncover (12 * dyadicDelta m) E := by
  set δ_m := dyadicDelta m with hδm
  have hδm_pos : 0 < δ_m := dyadicDelta_pos m

  -- First doubling: Ncover(3δ_m) ≤ D * Ncover(6δ_m)
  have h1 : Ncover (3 * δ_m) E ≤ (262144 : ENNReal) * Ncover (6 * δ_m) E := by
    have h_doub := affine_line_factor2_doubling (3 * δ_m) (by positivity) hE
    simpa [Ncover, show (2 * (3 * δ_m)) = 6 * δ_m by ring] using h_doub

  -- Second doubling: Ncover(6δ_m) ≤ D * Ncover(12δ_m)
  have h2 : Ncover (6 * δ_m) E ≤ (262144 : ENNReal) * Ncover (12 * δ_m) E := by
    have h_doub := affine_line_factor2_doubling (6 * δ_m) (by positivity) hE
    simpa [Ncover, show (2 * (6 * δ_m)) = 12 * δ_m by ring] using h_doub

  calc Ncover (3 * δ_m) E
    ≤ (262144 : ENNReal) * Ncover (6 * δ_m) E := h1
  _ ≤ (262144 : ENNReal) * ((262144 : ENNReal) * Ncover (12 * δ_m) E) := by gcongr
  _ = (262144 : ENNReal)^2 * Ncover (12 * δ_m) E := by ring

/-! ========================================================================
   Final combined lemma
   ======================================================================== -/

/-- Ncover(3δ_m, fineLines) ≤ 262144² * |coarseTubes| via root containment
    and two factor-2 doubling iterations.

    This is the Path 3 replacement for coarse_ncover_le_coarseCard when
    only root (standalone) containment C.toSet ⊆ U_stand.toSet is available,
    not project strip containment. -/
lemma coarse_ncover_3_le_coarseCard_via_root
    {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (h_slope_bound : ∀ T ∈ fineTubes, |T.slope| ≤ 1)
    (h_intercept_bound : ∀ T ∈ fineTubes, |T.intercept| ≤ 3)
    (h_parent : ∀ T ∈ fineTubes,
      ∃ (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m),
        C.a = T.a ∧
        |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 ∧
        C.toSet ⊆ U_stand.toSet ∧
        |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1 ∧
        Bridge.tubeToMainShifted U_stand ∈ coarseTubes) :
    Ncover (3 * dyadicDelta m)
      (toAffineLine '' (fineTubes : Set (DyadicTube n))) ≤
      (262144 : ENNReal)^2 * (coarseTubes.card : ENNReal) := by
  set E := toAffineLine '' (fineTubes : Set (DyadicTube n)) with hE_def

  have hE_bounded : ∀ ℓ ∈ E, ∃ (slope intercept : ℝ), |slope| ≤ 1 ∧ |intercept| ≤ 3 ∧
      lineOfSlopeIntercept slope intercept = ℓ := by
    intro ℓ hℓ
    have h_exists : ∃ (T : DyadicTube n), T ∈ fineTubes ∧ toAffineLine T = ℓ := by
      simpa [E, Set.mem_image] using hℓ
    rcases h_exists with ⟨T, hT, rfl⟩
    refine ⟨T.slope, T.intercept, h_slope_bound T hT, h_intercept_bound T hT, ?_⟩
    rfl

  have h12 : Ncover (12 * dyadicDelta m) E ≤ (coarseTubes.card : ENNReal) :=
    coarse_ncover_12_le_coarseCard_root hnm fineTubes coarseTubes
      h_slope_bound h_intercept_bound h_parent

  have h_doub : Ncover (3 * dyadicDelta m) E ≤
      (262144 : ENNReal)^2 * Ncover (12 * dyadicDelta m) E :=
    ncover_3_le_doubling_sq_of_12 E hE_bounded

  calc Ncover (3 * dyadicDelta m) E
    ≤ (262144 : ENNReal)^2 * Ncover (12 * dyadicDelta m) E := h_doub
  _ ≤ (262144 : ENNReal)^2 * (coarseTubes.card : ENNReal) := by gcongr

/-! ========================================================================
   B1InductionData integration helpers
   ======================================================================== -/

/-- Extract properties from C ∈ coveringCells n T.a T.b:
    C.a = T.a and |(C.b : ℝ) - (T.b : ℝ)| ≤ 1. -/
lemma coveringCells_props
    {n : ℕ} {a b : ℤ} {C : _root_.DyadicTube n}
    (hC : C ∈ Bridge.Geometric.coveringCells n a b) :
    C.a = a ∧ |(C.b : ℝ) - (b : ℝ)| ≤ 1 := by
  simp only [Bridge.Geometric.coveringCells, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with (rfl | rfl | rfl) <;> simp <;> norm_num

/-- Construct the h_parent existential from B1InductionData.h_tube_geometry. -/
lemma b1_data_to_parent
    {n m : ℕ} {hnm : m ≤ n}
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : DirecretisedFurstenbergEstimate.Section6.B1InductionData n m hnm s t C₁ M config)
    (T : DyadicTube n)
    (hT : T ∈ data.P.attach.biUnion (fun p => data.tubeFamily p p.property)) :
    ∃ (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m),
      C.a = T.a ∧
      |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 ∧
      C.toSet ⊆ U_stand.toSet ∧
      |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1 ∧
      Bridge.tubeToMainShifted U_stand ∈ data.coarseConfig.T₀ := by
  have h_exists : ∃ (p : {p // p ∈ data.P}),
      T ∈ data.tubeFamily p p.property := by
    rw [Finset.mem_biUnion] at hT
    rcases hT with ⟨p, _, hT_family⟩
    exact ⟨p, hT_family⟩
  rcases h_exists with ⟨p, hT_family⟩
  let hp : p.val ∈ data.P := p.property
  have h_geom := data.h_tube_geometry p.val hp T hT_family
  rcases h_geom with ⟨hQ, U_stand, C, hC_in, hU_in_family, h_contain⟩
  have hC_props := coveringCells_props (n := n) (a := T.a) (b := T.b) (C := C) hC_in
  have hU_in_T0 : Bridge.tubeToMainShifted U_stand ∈ data.coarseConfig.T₀ :=
    data.coarseConfig.h_subset
      (InductionConfigurations.containingSquare hnm p.val) hQ hU_in_family
  have h_U_slope : |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1 :=
    data.h_coarse_slope (Bridge.tubeToMainShifted U_stand) hU_in_T0
  exact ⟨C, U_stand, hC_props.1, hC_props.2, h_contain, h_U_slope, hU_in_T0⟩

/-- Full Ncover bound from B1InductionData via root containment + doubling.

    Given fine slope/intercept bounds indexed by DyadicSquare, produces:
    Ncover(3*δ_m, fineLines) ≤ 262144² * |data.coarseConfig.T₀|

    The fine tube set is the union of data.tubeFamily over data.P. -/
lemma b1_data_ncover_3_bound
    {n m : ℕ} {hnm : m ≤ n}
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : DirecretisedFurstenbergEstimate.Section6.B1InductionData n m hnm s t C₁ M config)
    (h_fine_slope : ∀ (p : DyadicSquare n) (hp : p ∈ data.P) (T : DyadicTube n),
      T ∈ data.tubeFamily p hp → |T.slope| ≤ 1)
    (h_fine_intercept : ∀ (p : DyadicSquare n) (hp : p ∈ data.P) (T : DyadicTube n),
      T ∈ data.tubeFamily p hp → |T.intercept| ≤ 3) :
    Ncover (3 * dyadicDelta m)
      (toAffineLine ''
        (data.P.attach.biUnion (fun p => data.tubeFamily p p.property) : Set (DyadicTube n))) ≤
      (262144 : ENNReal)^2 * (data.coarseConfig.T₀.card : ENNReal) := by
  let fineTubes : Finset (DyadicTube n) :=
    data.P.attach.biUnion (fun p => data.tubeFamily p p.property)
  let coarseTubes : Finset (DyadicTube m) := data.coarseConfig.T₀

  have h_slope_bound : ∀ T ∈ fineTubes, |T.slope| ≤ 1 := by
    intro T hT
    have h_exists : ∃ (p : {p // p ∈ data.P}),
        T ∈ data.tubeFamily p p.property := by
      rw [Finset.mem_biUnion] at hT
      rcases hT with ⟨p, _, hT_family⟩
      exact ⟨p, hT_family⟩
    rcases h_exists with ⟨p, hT_family⟩
    exact h_fine_slope p.val p.property T hT_family

  have h_intercept_bound : ∀ T ∈ fineTubes, |T.intercept| ≤ 3 := by
    intro T hT
    have h_exists : ∃ (p : {p // p ∈ data.P}),
        T ∈ data.tubeFamily p p.property := by
      rw [Finset.mem_biUnion] at hT
      rcases hT with ⟨p, _, hT_family⟩
      exact ⟨p, hT_family⟩
    rcases h_exists with ⟨p, hT_family⟩
    exact h_fine_intercept p.val p.property T hT_family

  have h_parent : ∀ T ∈ fineTubes,
      ∃ (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m),
        C.a = T.a ∧
        |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 ∧
        C.toSet ⊆ U_stand.toSet ∧
        |(Bridge.tubeToMainShifted U_stand).slope| ≤ 1 ∧
        Bridge.tubeToMainShifted U_stand ∈ coarseTubes := by
    intro T hT
    exact b1_data_to_parent data T hT

  exact coarse_ncover_3_le_coarseCard_via_root hnm fineTubes coarseTubes
    h_slope_bound h_intercept_bound h_parent

/-! ========================================================================
   Coefficient absorption adapter
   ======================================================================== -/

/-- Absorb the fixed doubling coefficient 262144² into loss_parent.

    Given:
      Ncover(3δ_m, retained) ≤ 262144² * NΔ
      Ncover(3δ_m, retained) ≥ (9δ_n)^(-(s+εA))
      262144² * 9^(s+εA) ≤ δ_n^(-loss_parent)

    Conclude:
      NΔ ≥ δ_n^(-(s+εA-loss_parent))

    The effective exponent is reduced by loss_parent, absorbing the constant. -/
lemma coarse_ncover_with_coefficient
    {δ_n : ℝ} (hδn_pos : 0 < δ_n)
    {s εA loss_parent : ℝ}
    (hloss_pos : 0 < loss_parent)
    {Ncover_val NΔ : ENNReal}
    (h : Ncover_val ≤ (262144 : ENNReal)^2 * NΔ)
    (h_app : ENNReal.ofReal ((9 * δ_n)^(-(s + εA))) ≤ Ncover_val)
    (h_absorb : (262144 : ℝ)^2 * (9 : ℝ)^(s + εA) ≤ δ_n^(-loss_parent)) :
    ENNReal.ofReal (δ_n^(-(s + εA - loss_parent))) ≤ NΔ := by
  set a : ℝ := (9 * δ_n)^(-(s + εA)) with ha_def
  set c : ℝ := (262144 : ℝ)^2 with hc_def
  have ha_pos : 0 < a := by positivity
  have hc_pos : 0 < c := by positivity
  have h9pos : 0 ≤ (9 : ℝ) := by norm_num
  let c' : ENNReal := ENNReal.ofReal c
  have hc'_pos : 0 < c' := by positivity

  -- Real inequality: a / c ≥ δ_n^(-(s+εA-loss_parent))
  have h_real : a / c ≥ δ_n^(-(s + εA - loss_parent)) := by
    have h1 : a = δ_n^(-(s + εA)) * (9 : ℝ)^(-(s + εA)) := by
      simp only [ha_def]
      have h2 : (9 * δ_n)^(-(s + εA)) = (9 : ℝ)^(-(s + εA)) * δ_n^(-(s + εA)) := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)] <;> ring
      have h2' : (9 * δ_n)^(-(s + εA)) = δ_n^(-(s + εA)) * (9 : ℝ)^(-(s + εA)) := by
        rw [h2, mul_comm]
      exact h2'
    have h3 : (9 : ℝ)^(-(s + εA)) = 1 / (9 : ℝ)^(s + εA) := by
      rw [Real.rpow_neg h9pos] <;> ring
    have h4 : a / c = δ_n^(-(s + εA)) / (c * (9 : ℝ)^(s + εA)) := by
      rw [h1, h3]
      field_simp [hc_def] <;> ring
    rw [h4]
    have h5 : c * (9 : ℝ)^(s + εA) ≤ δ_n^(-loss_parent) := h_absorb
    have h6 : 0 < c * (9 : ℝ)^(s + εA) := by positivity
    have h7 : δ_n^(-(s + εA)) / (c * (9 : ℝ)^(s + εA)) ≥
        δ_n^(-(s + εA)) / δ_n^(-loss_parent) := by gcongr
    have h8 : δ_n^(-(s + εA)) / δ_n^(-loss_parent) = δ_n^(-(s + εA - loss_parent)) := by
      have h9 : δ_n^(-(s + εA)) / δ_n^(-loss_parent) =
          δ_n^((-(s + εA)) - (-loss_parent)) := by
        rw [← Real.rpow_sub hδn_pos]
      rw [h9] <;> ring_nf
    rw [h8] at h7
    exact h7

  -- ENNReal manipulation
  let c' : ENNReal := ENNReal.ofReal c
  have hc'_pos : 0 < c' := by positivity
  have hc'_ne_top : c' ≠ ⊤ := by simp [c', hc_def] <;> norm_cast
  have hc'_eq : c' = (262144 : ENNReal)^2 := by
    simp [c', hc_def] <;> norm_cast

  have h_chain : ENNReal.ofReal a ≤ c' * NΔ := by
    rw [hc'_eq] at *
    exact le_trans h_app h

  let x : ℝ := a / c
  have hx_nonneg : 0 ≤ x := by positivity
  have h_x_mul : x * c = a := by
    dsimp only [x]
    field_simp [hc_pos.ne'] <;> ring

  have h_mul : ENNReal.ofReal (x * c) = ENNReal.ofReal x * c' := by
    have h_eq1 : ENNReal.ofReal (x * c) = ENNReal.ofReal x * ENNReal.ofReal c :=
      ENNReal.ofReal_mul hx_nonneg
    rw [h_eq1]
    <;> rfl

  have h4 : ENNReal.ofReal x * c' ≤ c' * NΔ := by
    have h5 : ENNReal.ofReal (x * c) = ENNReal.ofReal x * c' := h_mul
    have h6 : ENNReal.ofReal a ≤ c' * NΔ := h_chain
    have h7 : x * c = a := h_x_mul
    rw [h7] at h5
    rw [h5] at h6
    exact h6

  -- Cancel c' via toReal (split on NΔ = ⊤)
  have h_cancel : ENNReal.ofReal x ≤ NΔ := by
    by_cases hN : NΔ = ⊤
    · rw [hN]; exact le_top
    · have hN' : NΔ ≠ ⊤ := hN
      have h_ofReal_ne_top : ENNReal.ofReal x ≠ ⊤ := by simp
      have h_comm : c' * ENNReal.ofReal x = ENNReal.ofReal x * c' := by rw [mul_comm]
      have h4' : c' * ENNReal.ofReal x ≤ c' * NΔ := by
        rw [h_comm] <;> exact h4
      have h_mul_ne_top2 : c' * NΔ ≠ ⊤ := ENNReal.mul_ne_top hc'_ne_top hN
      have h_le_real : (c' * ENNReal.ofReal x).toReal ≤ (c' * NΔ).toReal :=
        ENNReal.toReal_mono h_mul_ne_top2 h4'
      have hc_nonneg : 0 ≤ c := by linarith
      have h_eq1 : (c' * ENNReal.ofReal x).toReal = c * x := by
        have h : (c' * ENNReal.ofReal x).toReal = c'.toReal * (ENNReal.ofReal x).toReal :=
          ENNReal.toReal_mul
        have h1 : c'.toReal = c := by
          simp [c', hc_nonneg]
        have h2 : (ENNReal.ofReal x).toReal = x := by
          simp [hx_nonneg]
        rw [h, h1, h2]
      have h_eq2 : (c' * NΔ).toReal = c * NΔ.toReal := by
        have h : (c' * NΔ).toReal = c'.toReal * NΔ.toReal := ENNReal.toReal_mul
        have h1 : c'.toReal = c := by
          simp [c', hc_nonneg]
        rw [h, h1]
      rw [h_eq1, h_eq2] at h_le_real
      have h_x_le : x ≤ NΔ.toReal := by nlinarith
      have h_goal : ENNReal.ofReal x ≤ NΔ := by
        rw [← ENNReal.ofReal_toReal hN']
        exact ENNReal.ofReal_le_ofReal h_x_le
      exact h_goal

  have h_last : ENNReal.ofReal (δ_n^(-(s + εA - loss_parent))) ≤ ENNReal.ofReal x :=
    ENNReal.ofReal_le_ofReal h_real
  exact le_trans h_last h_cancel

/-! ========================================================================
   Step 12: Coarse S-set from B1 induction data
   ======================================================================== -/

/-- Produce IsFinsetDeltaSSet on coarse parents from B1 induction data.

    Given fiber bounds on config_heavy (M_fiber ≤ |fiber| < 2*M_fiber) and
    B1 retention (|config_heavy fiber| ≤ data.K * |data.P fiber|), derive
    ratio fiber bounds on data.P with F_lo = M_fiber/data.K, R = 2*data.K.

    Then apply coarse_sset_from_ratio_fibers. -/
lemma b1_data_coarse_sset
    {n m : ℕ} (hnm : m ≤ n) (h_even : n = 2 * m)
    {s t u C₁ : ℝ} {M : ℕ}
    (config_heavy : CombiningTheorem.NiceConfiguration n s C₁ M)
    (data : B1InductionData n m hnm s t C₁ M config_heavy)
    (M_fiber : ℕ) (hM_fiber_pos : 0 < (M_fiber : ℝ))
    (hF0_lower : ∀ Q ∈ config_heavy.P₀.image (InductionConfigurations.containingSquare hnm),
        (M_fiber : ℝ) ≤ ((config_heavy.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ))
    (hF0_upper : ∀ Q ∈ config_heavy.P₀.image (InductionConfigurations.containingSquare hnm),
        ((config_heavy.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) < 2 * (M_fiber : ℝ))
    (C_point : ℝ) (hC_point_pos : 0 < C_point)
    (h_point_sset : IsDeltaSSet (dyadicDelta n) u C_point
        (⋃ p ∈ (data.P : Set (DyadicSquare n)), (p.toSet : Set Plane)))
    (hu_nonneg : 0 ≤ u) :
    IsFinsetDeltaSSet (dyadicDelta m) u
      (162 * C_point * (2 * data.K) * (2 * Real.sqrt 2) ^ u)
      (DyadicConversion.finsetDyadicToDSquare data.coarseConfig.P₀) := by
  let containSq := InductionConfigurations.containingSquare hnm
  let sqContain := InductionConfigurations.squareContained hnm
  let P_uniform := data.P
  let Q_uniform := data.coarseConfig.P₀
  let K_B1 : ℝ := data.K

  have hK_B1_ge1 : 1 ≤ K_B1 := data.hK_ge1
  have hK_B1_pos : 0 < K_B1 := by linarith

  have hP_sub : P_uniform ⊆ config_heavy.P₀ := data.hP_sub

  have hQ_eq : Q_uniform = P_uniform.image containSq := data.h_coarse_P_eq

  have hQ_nonempty : Q_uniform.Nonempty := by
    rw [hQ_eq]
    exact Finset.Nonempty.image data.hP_nonempty _

  have hQ_img_sub : P_uniform.image containSq ⊆ config_heavy.P₀.image containSq := by
    exact Finset.image_subset_image hP_sub

  let F_lo : ℝ := (M_fiber : ℝ) / K_B1
  have hF_lo_pos : 0 < F_lo := by
    dsimp only [F_lo]
    positivity

  let R : ℝ := 2 * K_B1
  have hR_ge_one : 1 ≤ R := by
    dsimp only [R]
    linarith [hK_B1_ge1]

  have h_fiber_lower : ∀ Q ∈ Q_uniform,
      F_lo ≤ ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) := by
    intro Q hQ
    have hQ_img : Q ∈ P_uniform.image containSq := by
      rw [hQ_eq] at hQ; exact hQ
    have hQ' : Q ∈ config_heavy.P₀.image containSq := hQ_img_sub hQ_img
    have h1 : ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) ≤
        K_B1 * ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) :=
      data.h_per_Q_ret Q hQ
    have h2 : (M_fiber : ℝ) ≤ ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) :=
      hF0_lower Q hQ'
    dsimp only [F_lo]
    have h3 : (M_fiber : ℝ) / K_B1 ≤ ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) / K_B1 := by
      gcongr
    have h4 : ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) / K_B1 ≤
        ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) := by
      have h5 : ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) ≤
          K_B1 * ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) := h1
      have h6 : ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) / K_B1 ≤
          (K_B1 * ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ)) / K_B1 := by gcongr
      have h7 : (K_B1 * ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ)) / K_B1 =
          ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) := by
        field_simp [hK_B1_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
    exact le_trans h3 h4

  have h_fiber_upper : ∀ Q ∈ Q_uniform,
      ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) < R * F_lo := by
    intro Q hQ
    have hQ_img : Q ∈ P_uniform.image containSq := by
      rw [hQ_eq] at hQ; exact hQ
    have hQ' : Q ∈ config_heavy.P₀.image containSq := hQ_img_sub hQ_img
    have h_sub : P_uniform.filter (fun p => sqContain p Q) ⊆
        config_heavy.P₀.filter (fun p => sqContain p Q) := by
      intro p hp
      have hp1 : p ∈ P_uniform := (Finset.mem_filter.mp hp).1
      have hp2 : p ∈ config_heavy.P₀ := hP_sub hp1
      exact Finset.mem_filter.mpr ⟨hp2, (Finset.mem_filter.mp hp).2⟩
    have h_card : (P_uniform.filter (fun p => sqContain p Q)).card ≤
        (config_heavy.P₀.filter (fun p => sqContain p Q)).card :=
      Finset.card_le_card h_sub
    have h_card' : ((P_uniform.filter (fun p => sqContain p Q)).card : ℝ) ≤
        ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) := by
      exact_mod_cast h_card
    have h_upper : ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) < 2 * (M_fiber : ℝ) :=
      hF0_upper Q hQ'
    have h_eq : R * F_lo = 2 * (M_fiber : ℝ) := by
      dsimp only [R, F_lo]
      field_simp [hK_B1_pos.ne'] <;> ring
    rw [h_eq]
    exact lt_of_le_of_lt h_card' h_upper

  exact CombiningTheoremRework.coarse_sset_from_ratio_fibers (K_P := 0) hnm h_even config_heavy P_uniform hP_sub
    Q_uniform hQ_eq hQ_nonempty F_lo hF_lo_pos R hR_ge_one
    h_fiber_lower h_fiber_upper h_point_sset hu_nonneg hC_point_pos

end DiscretisedFurstenbergEstimate.CoveringUtils

end
