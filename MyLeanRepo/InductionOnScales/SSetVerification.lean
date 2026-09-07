module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# SSet Verification for Coarse Tube Family

Transfer the SSet property from fine families to a coarse family via
double-counting and averaging (OS lines 622-636).

Main result: `coarse_sset_verification`.

Whiteprint node: `InductionOnScales/Proposition2/SSetVerification`
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

-- ============================================================================
-- 1. Unique coarse ancestor
-- ============================================================================

/-- A fine tube is contained in exactly one coarse tube: its coarse ancestor. -/
lemma unique_coarse_ancestor {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (hcont : T.toSet ⊆ U.toSet) :
    U = deprecatedCoordinatewiseAncestor hnm T := by
  set f : ℕ := coarseRefinementFactor n m with hf
  have h_main := (tube_containment_iff hnm T U).mp hcont
  have ha1 : (U.a : ℤ) * (f : ℤ) ≤ T.a := h_main.1
  have ha2 : T.a + 1 ≤ (U.a + 1) * (f : ℤ) := h_main.2.1
  have hb1 : (U.b : ℤ) * (f : ℤ) ≤ T.b := h_main.2.2.1
  have hb2 : T.b + 1 ≤ (U.b + 1) * (f : ℤ) := h_main.2.2.2
  have hf_pos : 0 < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hfa : (U.a : ℝ) ≤ (T.a : ℝ) / (f : ℝ) := by
    have h : (U.a : ℝ) * (f : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast ha1
    have h' : (U.a : ℝ) ≤ (T.a : ℝ) / (f : ℝ) := by
      calc (U.a : ℝ)
        = ((U.a : ℝ) * (f : ℝ)) / (f : ℝ) := by field_simp [hf_pos.ne'] <;> ring
      _ ≤ (T.a : ℝ) / (f : ℝ) := by gcongr
    exact h'
  have hga : (T.a : ℝ) / (f : ℝ) < (U.a : ℝ) + 1 := by
    have h : (T.a : ℝ) < ((U.a : ℝ) + 1) * (f : ℝ) := by
      have h' : T.a + 1 ≤ (U.a + 1) * (f : ℤ) := ha2
      exact_mod_cast (by linarith)
    have h' : (T.a : ℝ) / (f : ℝ) < ((U.a : ℝ) + 1) := by
      calc (T.a : ℝ) / (f : ℝ)
        < (((U.a : ℝ) + 1) * (f : ℝ)) / (f : ℝ) := by gcongr
      _ = (U.a : ℝ) + 1 := by field_simp [hf_pos.ne'] <;> ring
    exact h'
  have hfb : (U.b : ℝ) ≤ (T.b : ℝ) / (f : ℝ) := by
    have h : (U.b : ℝ) * (f : ℝ) ≤ (T.b : ℝ) := by exact_mod_cast hb1
    have h' : (U.b : ℝ) ≤ (T.b : ℝ) / (f : ℝ) := by
      calc (U.b : ℝ)
        = ((U.b : ℝ) * (f : ℝ)) / (f : ℝ) := by field_simp [hf_pos.ne'] <;> ring
      _ ≤ (T.b : ℝ) / (f : ℝ) := by gcongr
    exact h'
  have hgb : (T.b : ℝ) / (f : ℝ) < (U.b : ℝ) + 1 := by
    have h : (T.b : ℝ) < ((U.b : ℝ) + 1) * (f : ℝ) := by
      have h' : T.b + 1 ≤ (U.b + 1) * (f : ℤ) := hb2
      exact_mod_cast (by linarith)
    have h' : (T.b : ℝ) / (f : ℝ) < ((U.b : ℝ) + 1) := by
      calc (T.b : ℝ) / (f : ℝ)
        < (((U.b : ℝ) + 1) * (f : ℝ)) / (f : ℝ) := by gcongr
      _ = (U.b : ℝ) + 1 := by field_simp [hf_pos.ne'] <;> ring
    exact h'
  have h_floor_a : ⌊(T.a : ℝ) / (f : ℝ)⌋ = U.a := by
    rw [Int.floor_eq_iff] <;> exact ⟨hfa, hga⟩
  have h_floor_b : ⌊(T.b : ℝ) / (f : ℝ)⌋ = U.b := by
    rw [Int.floor_eq_iff] <;> exact ⟨hfb, hgb⟩
  let U' := deprecatedCoordinatewiseAncestor hnm T
  have hU'_a : U'.a = ⌊(T.a : ℝ) / (f : ℝ)⌋ := by
    simp [U', deprecatedCoordinatewiseAncestor, coarseParentIndex] <;> rfl
  have hU'_b : U'.b = ⌊(T.b : ℝ) / (f : ℝ)⌋ := by
    simp [U', deprecatedCoordinatewiseAncestor, coarseParentIndex] <;> rfl
  have h_a : U.a = U'.a := by
    calc U.a = ⌊(T.a : ℝ) / (f : ℝ)⌋ := h_floor_a.symm
         _ = U'.a := hU'_a.symm
  have h_b : U.b = U'.b := by
    calc U.b = ⌊(T.b : ℝ) / (f : ℝ)⌋ := h_floor_b.symm
         _ = U'.b := hU'_b.symm
  have h_eq : U = U' := by
    have h1 : U = DyadicTube.mk U.a U.b := by cases U <;> rfl
    have h2 : U' = DyadicTube.mk U'.a U'.b := by cases U' <;> rfl
    rw [h1, h2, h_a, h_b]
  exact h_eq

/-- Fine tubes contained in distinct coarse tubes are disjoint. -/
lemma fine_tubes_in_distinct_coarse_disjoint {n m : ℕ} (hnm : m ≤ n)
    (U₁ U₂ : DyadicTube m) (hne : U₁ ≠ U₂)
    (T : DyadicTube n)
    (h1 : T.toSet ⊆ U₁.toSet) (h2 : T.toSet ⊆ U₂.toSet) : False := by
  have h3 : U₁ = deprecatedCoordinatewiseAncestor hnm T :=
    unique_coarse_ancestor hnm T U₁ h1
  have h4 : U₂ = deprecatedCoordinatewiseAncestor hnm T :=
    unique_coarse_ancestor hnm T U₂ h2
  have h5 : U₁ = U₂ := by
    rw [h3, h4]
  exact hne h5

-- ============================================================================
-- 2. Parameter distance bridge
-- ============================================================================

/-- Embed a coarse tube as a fine tube at the same parameter location. -/
def embedCoarseTube {n m : ℕ} (hnm : m ≤ n) (V : DyadicTube m) : DyadicTube n :=
  ⟨V.a * (coarseRefinementFactor n m : ℤ),
   V.b * (coarseRefinementFactor n m : ℤ)⟩

lemma embedCoarseTube_slope {n m : ℕ} (hnm : m ≤ n) (V : DyadicTube m) :
    (embedCoarseTube hnm V).slope = V.slope := by
  set f : ℕ := coarseRefinementFactor n m with hf
  set δ := dyadicDelta n with hδ
  set Δ := dyadicDelta m with hΔ
  have h_rel : δ = Δ / (f : ℝ) := dyadicDelta_ratio n m hnm
  have hf_pos : 0 < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have h1 : (embedCoarseTube hnm V).slope = ((V.a * (f : ℤ)) : ℝ) * δ := by
    simp [embedCoarseTube, DyadicTube.slope] <;> norm_cast <;> ring
  rw [h1]
  have h2 : ((V.a * (f : ℤ)) : ℝ) * δ = (V.a : ℝ) * Δ := by
    have h3 : ((V.a * (f : ℤ)) : ℝ) = (V.a : ℝ) * (f : ℝ) := by norm_cast <;> ring
    rw [h3]
    have h4 : (V.a : ℝ) * (f : ℝ) * δ = (V.a : ℝ) * Δ := by
      rw [h_rel]
      field_simp [hf_pos.ne'] <;> ring
    exact h4
  rw [h2] <;> rfl

lemma embedCoarseTube_intercept {n m : ℕ} (hnm : m ≤ n) (V : DyadicTube m) :
    (embedCoarseTube hnm V).intercept = V.intercept := by
  set f : ℕ := coarseRefinementFactor n m with hf
  set δ := dyadicDelta n with hδ
  set Δ := dyadicDelta m with hΔ
  have h_rel : δ = Δ / (f : ℝ) := dyadicDelta_ratio n m hnm
  have hf_pos : 0 < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have h1 : (embedCoarseTube hnm V).intercept = ((V.b * (f : ℤ)) : ℝ) * δ := by
    simp [embedCoarseTube, DyadicTube.intercept] <;> norm_cast <;> ring
  rw [h1]
  have h2 : ((V.b * (f : ℤ)) : ℝ) * δ = (V.b : ℝ) * Δ := by
    have h3 : ((V.b * (f : ℤ)) : ℝ) = (V.b : ℝ) * (f : ℝ) := by norm_cast <;> ring
    rw [h3]
    have h4 : (V.b : ℝ) * (f : ℝ) * δ = (V.b : ℝ) * Δ := by
      rw [h_rel]
      field_simp [hf_pos.ne'] <;> ring
    exact h4
  rw [h2] <;> rfl

/-- If fine T ⊆ coarse U and dist(U,V) ≤ r, then dist(T, embed V) ≤ r + Δ. -/
lemma contained_tube_paramDist_bound {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U V : DyadicTube m)
    (hcont : T.toSet ⊆ U.toSet) (r : ℝ)
    (hr : tubeParamDist U V ≤ r) :
    tubeParamDist T (embedCoarseTube hnm V) ≤ r + dyadicDelta m := by
  set Δ := dyadicDelta m with hΔ_def
  set δ := dyadicDelta n with hδ_def
  set f := coarseRefinementFactor n m with hf
  have h_rel : δ = Δ / (f : ℝ) := dyadicDelta_ratio n m hnm
  have hf_pos : 0 < (f : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  have h_main := (tube_containment_iff hnm T U).mp hcont
  have h_slope_U : |U.slope - V.slope| ≤ r := by
    have h : tubeParamDist U V = max |U.slope - V.slope| |U.intercept - V.intercept| := rfl
    rw [h] at hr
    exact le_trans (le_max_left _ _) hr
  have h_intercept_U : |U.intercept - V.intercept| ≤ r := by
    have h : tubeParamDist U V = max |U.slope - V.slope| |U.intercept - V.intercept| := rfl
    rw [h] at hr
    exact le_trans (le_max_right _ _) hr
  have hV_slope : (embedCoarseTube hnm V).slope = V.slope := embedCoarseTube_slope hnm V
  have hV_intercept : (embedCoarseTube hnm V).intercept = V.intercept := embedCoarseTube_intercept hnm V
  have h_T_slope1 : U.slope ≤ T.slope := by
    have h' : (U.a : ℤ) * (f : ℤ) ≤ T.a := h_main.1
    have h'' : (U.a : ℝ) * (f : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h'
    have h3 : (U.a : ℝ) * Δ ≤ (T.a : ℝ) * δ := by
      calc (U.a : ℝ) * Δ
        = ((U.a : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
      _ = ((U.a : ℝ) * (f : ℝ)) * δ := by rw [h_rel]
      _ ≤ (T.a : ℝ) * δ := by gcongr
    simpa [DyadicTube.slope] using h3
  have h_T_slope2 : T.slope ≤ U.slope + Δ := by
    have h' : T.a + 1 ≤ (U.a + 1) * (f : ℤ) := h_main.2.1
    have h'' : (T.a + 1 : ℝ) ≤ (U.a + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h'
    have h_posdiv : 0 ≤ Δ / (f : ℝ) := div_nonneg hΔ_pos.le hf_pos.le
    have h_a1 : (T.a : ℝ) ≤ (T.a + 1 : ℝ) := by simp <;> linarith
    have h_step1 : (T.a : ℝ) * (Δ / (f : ℝ)) ≤ (T.a + 1 : ℝ) * (Δ / (f : ℝ)) :=
      mul_le_mul_of_nonneg_right h_a1 h_posdiv
    have h_step2 : (T.a + 1 : ℝ) * (Δ / (f : ℝ)) ≤ ((U.a + 1 : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) :=
      mul_le_mul_of_nonneg_right h'' h_posdiv
    have h3 : (T.a : ℝ) * δ ≤ (U.a + 1 : ℝ) * Δ := by
      calc (T.a : ℝ) * δ
        = (T.a : ℝ) * (Δ / (f : ℝ)) := by rw [h_rel]
      _ ≤ (T.a + 1 : ℝ) * (Δ / (f : ℝ)) := h_step1
      _ ≤ ((U.a + 1 : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) := h_step2
      _ = (U.a + 1 : ℝ) * Δ := by field_simp [hf_pos.ne'] <;> ring
    have h4 : T.slope = (T.a : ℝ) * δ := by rfl
    have h5 : U.slope + Δ = (U.a : ℝ) * Δ + Δ := by rfl
    rw [h4, h5] <;> linarith
  have h_T_intercept1 : U.intercept ≤ T.intercept := by
    have h' : (U.b : ℤ) * (f : ℤ) ≤ T.b := h_main.2.2.1
    have h'' : (U.b : ℝ) * (f : ℝ) ≤ (T.b : ℝ) := by exact_mod_cast h'
    have h3 : (U.b : ℝ) * Δ ≤ (T.b : ℝ) * δ := by
      calc (U.b : ℝ) * Δ
        = ((U.b : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) := by field_simp [hf_pos.ne'] <;> ring
      _ = ((U.b : ℝ) * (f : ℝ)) * δ := by rw [h_rel]
      _ ≤ (T.b : ℝ) * δ := by gcongr
    simpa [DyadicTube.intercept] using h3
  have h_T_intercept2 : T.intercept ≤ U.intercept + Δ := by
    have h' : T.b + 1 ≤ (U.b + 1) * (f : ℤ) := h_main.2.2.2
    have h'' : (T.b + 1 : ℝ) ≤ (U.b + 1 : ℝ) * (f : ℝ) := by exact_mod_cast h'
    have h_posdiv : 0 ≤ Δ / (f : ℝ) := div_nonneg hΔ_pos.le hf_pos.le
    have h_b1 : (T.b : ℝ) ≤ (T.b + 1 : ℝ) := by simp <;> linarith
    have h_step1 : (T.b : ℝ) * (Δ / (f : ℝ)) ≤ (T.b + 1 : ℝ) * (Δ / (f : ℝ)) :=
      mul_le_mul_of_nonneg_right h_b1 h_posdiv
    have h_step2 : (T.b + 1 : ℝ) * (Δ / (f : ℝ)) ≤ ((U.b + 1 : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) :=
      mul_le_mul_of_nonneg_right h'' h_posdiv
    have h3 : (T.b : ℝ) * δ ≤ (U.b + 1 : ℝ) * Δ := by
      calc (T.b : ℝ) * δ
        = (T.b : ℝ) * (Δ / (f : ℝ)) := by rw [h_rel]
      _ ≤ (T.b + 1 : ℝ) * (Δ / (f : ℝ)) := h_step1
      _ ≤ ((U.b + 1 : ℝ) * (f : ℝ)) * (Δ / (f : ℝ)) := h_step2
      _ = (U.b + 1 : ℝ) * Δ := by field_simp [hf_pos.ne'] <;> ring
    have h4 : T.intercept = (T.b : ℝ) * δ := by rfl
    have h5 : U.intercept + Δ = (U.b : ℝ) * Δ + Δ := by rfl
    rw [h4, h5] <;> linarith
  have h_slope_dist : |T.slope - (embedCoarseTube hnm V).slope| ≤ r + Δ := by
    rw [hV_slope, abs_le] <;> constructor <;> linarith [abs_le.mp h_slope_U]
  have h_intercept_dist : |T.intercept - (embedCoarseTube hnm V).intercept| ≤ r + Δ := by
    rw [hV_intercept, abs_le] <;> constructor <;> linarith [abs_le.mp h_intercept_U]
  have h : tubeParamDist T (embedCoarseTube hnm V) =
      max |T.slope - (embedCoarseTube hnm V).slope|
          |T.intercept - (embedCoarseTube hnm V).intercept| := rfl
  rw [h]
  exact max_le h_slope_dist h_intercept_dist

-- ============================================================================
-- 3. Minimum separation for distinct coarse tubes
-- ============================================================================

/-- Distinct coarse tubes have parameter distance at least Δ. -/
lemma coarse_tubes_separation {m : ℕ} (U V : DyadicTube m) (hne : U ≠ V) :
    dyadicDelta m ≤ tubeParamDist U V := by
  set Δ := dyadicDelta m with hΔ_def
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  by_cases ha : U.a ≠ V.a
  · have h_diff : 1 ≤ |(U.a : ℝ) - (V.a : ℝ)| := by
      have h_ne : (U.a - V.a : ℤ) ≠ 0 := by omega
      have h : 1 ≤ |U.a - V.a| := Int.one_le_abs h_ne
      exact_mod_cast h
    have h_eq : |U.slope - V.slope| = Δ * |(U.a : ℝ) - (V.a : ℝ)| := by
      have h_slope : U.slope - V.slope = ((U.a : ℝ) - (V.a : ℝ)) * Δ := by
        simp [DyadicTube.slope, hΔ_def] <;> ring
      rw [h_slope]
      rw [abs_mul, abs_of_pos hΔ_pos] <;> ring
    have h2 : Δ ≤ |U.slope - V.slope| := by
      rw [h_eq]
      have h3 : 0 ≤ Δ := hΔ_pos.le
      nlinarith
    have h4 : |U.slope - V.slope| ≤ tubeParamDist U V := le_max_left _ _
    linarith
  · have h_a : U.a = V.a := by tauto
    have h_b : U.b ≠ V.b := by
      intro h
      apply hne
      have h1 : U = V := by
        cases U <;> cases V <;> simp_all (config := {decide := true})
      exact h1
    have h_diff : 1 ≤ |(U.b : ℝ) - (V.b : ℝ)| := by
      have h_ne : (U.b - V.b : ℤ) ≠ 0 := by omega
      have h : 1 ≤ |U.b - V.b| := Int.one_le_abs h_ne
      exact_mod_cast h
    have h_eq : |U.intercept - V.intercept| = Δ * |(U.b : ℝ) - (V.b : ℝ)| := by
      have h_intercept : U.intercept - V.intercept = ((U.b : ℝ) - (V.b : ℝ)) * Δ := by
        simp [DyadicTube.intercept, hΔ_def] <;> ring
      rw [h_intercept]
      rw [abs_mul, abs_of_pos hΔ_pos] <;> ring
    have h2 : Δ ≤ |U.intercept - V.intercept| := by
      rw [h_eq]
      have h3 : 0 ≤ Δ := hΔ_pos.le
      nlinarith
    have h4 : |U.intercept - V.intercept| ≤ tubeParamDist U V := le_max_right _ _
    linarith

-- ============================================================================
-- 4. Main SSet verification theorem
-- ============================================================================

/-- Transfer the SSet property from fine families to a coarse family via
double-counting and averaging (OS lines 622-636). -/
theorem coarse_sset_verification
    {n m : ℕ} (hnm : m ≤ n)
    {α : Type*} [DecidableEq α]
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM_pos : 0 < M)
    (TΔ : Finset (DyadicTube m)) (hTΔ_nonempty : TΔ.Nonempty)
    (P : Finset α) (hP_nonempty : P.Nonempty)
    (coarseFamily : α → Finset (DyadicTube m))
    (fineFamily : α → Finset (DyadicTube n))
    (m₁ : ℕ) (hm₁_pos : 0 < m₁)
    (L : ℕ) (hL_pos : 0 < L)
    (K : ℝ) (hK : 1 ≤ K)
    (h_coarse_sub : ∀ p ∈ P, coarseFamily p ⊆ TΔ)
    (h_pop : ∀ U ∈ TΔ, (P.filter (fun p => U ∈ coarseFamily p)).card ≥ L)
    (h_fine_per_coarse : ∀ p ∈ P, ∀ U ∈ coarseFamily p,
        ((fineFamily p).filter (fun T => T.toSet ⊆ U.toSet)).card ≥ m₁)
    (h_fine_sset : ∀ p ∈ P, IsFiniteTubeSSet s C₁ (fineFamily p))
    (h_fine_size : ∀ p ∈ P, (fineFamily p).card = M)
    (h_relation : (m₁ : ℝ) * (L : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) :
    IsFiniteTubeSSet s (K * 2 * C₁) TΔ := by
  have h_sep : ∀ U ∈ TΔ, ∀ V ∈ TΔ, U ≠ V → dyadicDelta m ≤ tubeParamDist U V := by
    intro U _ V _ hne
    exact coarse_tubes_separation U V hne
  have h_const : 1 ≤ K * 2 * C₁ := by
    have h1 : 1 ≤ C₁ := hC₁
    have h2 : 1 ≤ K := hK
    nlinarith
  have h_ball : ∀ (center : DyadicTube m) (r : ℝ), dyadicDelta m ≤ r →
      ((TΔ.filter fun U => tubeParamDist U center ≤ r).card : ℝ) ≤
        (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by
    intro center r hr
    set B := TΔ.filter fun U => tubeParamDist U center ≤ r with hB_def
    by_cases hB_empty : B = ∅
    · rw [hB_empty]
      simp
      <;> have h_pos : 0 ≤ (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by
        have hr_pos : 0 ≤ r := by linarith [dyadicDelta_pos m]
        have h_rpow : 0 ≤ Real.rpow r s := Real.rpow_nonneg hr_pos s
        positivity
      exact h_pos
    · have hB_nonempty : B.Nonempty := by
        simpa [hB_def, Finset.nonempty_iff_ne_empty] using hB_empty
      set V' := embedCoarseTube hnm center with hV'_def
      set R := r + dyadicDelta m with hR_def

      have h_each_pop : ∀ U ∈ B, (L : ℝ) ≤ ((P.filter (fun p => U ∈ coarseFamily p)).card : ℝ) := by
        intro U hU
        have hU_in_TΔ : U ∈ TΔ := (Finset.mem_filter.mp hU).1
        exact_mod_cast h_pop U hU_in_TΔ

      have h_total_inc : (B.card : ℝ) * (L : ℝ) ≤
          ∑ U ∈ B, ((P.filter (fun p => U ∈ coarseFamily p)).card : ℝ) := by
        have h1 : (B.card : ℝ) * (L : ℝ) = ∑ U ∈ B, (L : ℝ) := by
          simp [Finset.sum_const] <;> ring
        rw [h1]
        apply Finset.sum_le_sum
        exact h_each_pop

      have h_card_as_sum : ∀ (U : DyadicTube m),
          ((P.filter (fun p => U ∈ coarseFamily p)).card : ℝ) =
          ∑ p ∈ P, (if U ∈ coarseFamily p then (1 : ℝ) else 0) := by
        intro U
        simp [Finset.filter]
        <;> rfl

      have h_swap : ∑ U ∈ B, ((P.filter (fun p => U ∈ coarseFamily p)).card : ℝ) =
          ∑ p ∈ P, ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) := by
        have h1 : ∑ U ∈ B, ((P.filter (fun p => U ∈ coarseFamily p)).card : ℝ) =
            ∑ U ∈ B, ∑ p ∈ P, (if U ∈ coarseFamily p then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro U _
          exact h_card_as_sum U
        rw [h1]
        have h2 : ∑ U ∈ B, ∑ p ∈ P, (if U ∈ coarseFamily p then (1 : ℝ) else 0) =
            ∑ p ∈ P, ∑ U ∈ B, (if U ∈ coarseFamily p then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
        rw [h2]
        apply Finset.sum_congr rfl
        intro p _
        have h3 : ∑ U ∈ B, (if U ∈ coarseFamily p then (1 : ℝ) else 0) =
            ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) := by
          simp [Finset.filter]
          <;> rfl
        rw [h3]

      have h_avg : ∃ p₀ ∈ P, ((B.filter (fun U => U ∈ coarseFamily p₀)).card : ℝ) ≥
          (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) := by
        by_contra h
        push Not at h
        have h_sum : ∑ p ∈ P, ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) <
            (B.card : ℝ) * (L : ℝ) := by
          calc ∑ p ∈ P, ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ)
            < ∑ p ∈ P, ((B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) :=
              Finset.sum_lt_sum_of_nonempty hP_nonempty (fun p hp => h p hp)
          _ = (B.card : ℝ) * (L : ℝ) := by
            simp [Finset.sum_const] <;> field_simp <;> ring
        have h_contra : ∑ p ∈ P, ((B.filter (fun U => U ∈ coarseFamily p)).card : ℝ) < (B.card : ℝ) * (L : ℝ) := h_sum
        rw [←h_swap] at h_contra
        linarith [h_total_inc]

      rcases h_avg with ⟨p₀, hp₀, h_p₀_bound⟩
      set Bp := B.filter (fun U => U ∈ coarseFamily p₀) with hBp_def
      set fineInB := Finset.biUnion Bp (fun U =>
          (fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)) with hfineInB_def

      have h_disj : ∀ U₁ ∈ Bp, ∀ U₂ ∈ Bp, U₁ ≠ U₂ →
          Disjoint ((fineFamily p₀).filter (fun T => T.toSet ⊆ U₁.toSet))
                   ((fineFamily p₀).filter (fun T => T.toSet ⊆ U₂.toSet)) := by
        intro U₁ hU₁ U₂ hU₂ hne
        rw [Finset.disjoint_left]
        intro T hT1 hT2
        have h1 : T.toSet ⊆ U₁.toSet := (Finset.mem_filter.mp hT1).2
        have h2 : T.toSet ⊆ U₂.toSet := (Finset.mem_filter.mp hT2).2
        exact fine_tubes_in_distinct_coarse_disjoint hnm U₁ U₂ hne T h1 h2

      have h_card_union : (fineInB.card : ℝ) =
          ∑ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) := by
        rw [hfineInB_def, Finset.card_biUnion h_disj]
        <;> norm_cast

      have h_each : ∀ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) ≥ (m₁ : ℝ) := by
        intro U hU
        have hU_in_coarse : U ∈ coarseFamily p₀ := (Finset.mem_filter.mp hU).2
        exact_mod_cast h_fine_per_coarse p₀ hp₀ U hU_in_coarse

      have h_lower : (fineInB.card : ℝ) ≥ (m₁ : ℝ) * (Bp.card : ℝ) := by
        rw [h_card_union]
        have h : ∑ U ∈ Bp, (((fineFamily p₀).filter (fun T => T.toSet ⊆ U.toSet)).card : ℝ) ≥
            ∑ U ∈ Bp, (m₁ : ℝ) := Finset.sum_le_sum h_each
        have h2 : ∑ U ∈ Bp, (m₁ : ℝ) = (m₁ : ℝ) * (Bp.card : ℝ) := by
          simp [Finset.sum_const] <;> ring
        linarith

      have h_subset : fineInB ⊆ (fineFamily p₀).filter (fun T => tubeParamDist T V' ≤ R) := by
        intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨U, hU, hT_in⟩
        have hT_in_fine : T ∈ fineFamily p₀ := (Finset.mem_filter.mp hT_in).1
        have hT_cont : T.toSet ⊆ U.toSet := (Finset.mem_filter.mp hT_in).2
        have hU_in_B : U ∈ B := (Finset.mem_filter.mp hU).1
        have hU_dist : tubeParamDist U center ≤ r := (Finset.mem_filter.mp hU_in_B).2
        have hT_dist : tubeParamDist T V' ≤ R :=
          contained_tube_paramDist_bound hnm T U center hT_cont r hU_dist
        exact Finset.mem_filter.mpr ⟨hT_in_fine, hT_dist⟩

      have h1 : dyadicDelta n ≤ dyadicDelta m := by
        have h2 : (n : ℝ) ≥ (m : ℝ) := by exact_mod_cast hnm
        have h3 : (-(n : ℝ)) ≤ (-(m : ℝ)) := by linarith
        have h4 : Real.rpow 2 (-(n : ℝ)) ≤ Real.rpow 2 (-(m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 from by norm_num) h3
        simpa [dyadicDelta] using h4
      have hR_ge : dyadicDelta n ≤ R := by
        have h3 : dyadicDelta n ≤ dyadicDelta m := h1
        have h4 : dyadicDelta m ≤ R := by
          simp [hR_def] <;> linarith [dyadicDelta_pos m]
        linarith

      rcases h_fine_sset p₀ hp₀ with ⟨_, _, _, _, h_frostman⟩
      have h_sset := h_frostman V' R hR_ge

      have h_upper : (fineInB.card : ℝ) ≤
          C₁ * Real.rpow R s * ((fineFamily p₀).card : ℝ) := by
        have h5 : (fineInB.card : ℝ) ≤
            (((fineFamily p₀).filter (fun T => tubeParamDist T V' ≤ R)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h_subset
        have h6 := h_sset
        rw [h_fine_size p₀ hp₀] at h6
        linarith

      have h_M : ((fineFamily p₀).card : ℝ) = (M : ℝ) := by
        rw [h_fine_size p₀ hp₀] <;> norm_cast
      rw [h_M] at h_upper

      have h_rpow : Real.rpow R s ≤ 2 * Real.rpow r s := by
        have h7 : R ≤ 2 * r := by
          dsimp only [R]
          have h_le : dyadicDelta m ≤ r := hr
          linarith
        have h8 : 0 ≤ R := by
          dsimp only [R]
          have h9 : 0 ≤ r := by linarith [dyadicDelta_pos m]
          have h10 : 0 ≤ dyadicDelta m := (dyadicDelta_pos m).le
          linarith
        have h9 : Real.rpow R s ≤ Real.rpow (2 * r) s :=
          Real.rpow_le_rpow h8 h7 hs
        have h10 : Real.rpow (2 * r) s = Real.rpow 2 s * Real.rpow r s :=
          Real.mul_rpow (show (0 : ℝ) ≤ 2 from by norm_num) (show 0 ≤ r from by linarith)
        have h11 : Real.rpow R s ≤ Real.rpow 2 s * Real.rpow r s := by
          calc Real.rpow R s ≤ Real.rpow (2 * r) s := h9
               _ = Real.rpow 2 s * Real.rpow r s := h10
        have h12 : Real.rpow 2 s ≤ 2 := by
          have h13 : s ≤ 1 := hs_one
          have h14 : Real.rpow 2 s ≤ Real.rpow 2 1 :=
            Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 from by norm_num) h13
          simpa using h14
        have h15 : Real.rpow R s ≤ 2 * Real.rpow r s := by
          calc Real.rpow R s
            ≤ Real.rpow 2 s * Real.rpow r s := h11
          _ ≤ 2 * Real.rpow r s := by
            have h16 : 0 ≤ Real.rpow r s := Real.rpow_nonneg (by linarith) s
            nlinarith
        exact h15

      have h_final : (B.card : ℝ) ≤ (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by
        have h1 : (m₁ : ℝ) * (Bp.card : ℝ) ≤ (fineInB.card : ℝ) := h_lower
        have h2 : (Bp.card : ℝ) ≥ (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) := h_p₀_bound
        have h3 : (m₁ : ℝ) * (B.card : ℝ) * (L : ℝ) / (P.card : ℝ) ≤ (fineInB.card : ℝ) := by
          calc (m₁ : ℝ) * (B.card : ℝ) * (L : ℝ) / (P.card : ℝ)
            = (m₁ : ℝ) * ((B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) := by ring
          _ ≤ (m₁ : ℝ) * (Bp.card : ℝ) := by gcongr
          _ ≤ (fineInB.card : ℝ) := h1
        have h4 : (fineInB.card : ℝ) ≤ C₁ * Real.rpow R s * (M : ℝ) := h_upper
        have h5 : (m₁ : ℝ) * (L : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ)) := h_relation
        have hP_pos : 0 < (P.card : ℝ) := by exact_mod_cast hP_nonempty.card_pos
        have hT_pos : 0 < (TΔ.card : ℝ) := by exact_mod_cast hTΔ_nonempty.card_pos
        have hM_pos' : 0 < (M : ℝ) := by exact_mod_cast hM_pos
        have h6 : (m₁ : ℝ) * (B.card : ℝ) * (L : ℝ) ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by
          calc (m₁ : ℝ) * (B.card : ℝ) * (L : ℝ)
            = ((m₁ : ℝ) * (B.card : ℝ) * (L : ℝ) / (P.card : ℝ)) * (P.card : ℝ) := by field_simp [hP_pos.ne'] <;> ring
          _ ≤ (fineInB.card : ℝ) * (P.card : ℝ) := by gcongr
          _ ≤ (C₁ * Real.rpow R s * (M : ℝ)) * (P.card : ℝ) := by gcongr
          _ = C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by ring
        have h7 : (B.card : ℝ) * ((M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) ≤ (B.card : ℝ) * ((m₁ : ℝ) * (L : ℝ)) := by
          gcongr
        have h8 : (B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ)) ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := by
          calc (B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))
            = (B.card : ℝ) * ((M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) := by ring
          _ ≤ (B.card : ℝ) * ((m₁ : ℝ) * (L : ℝ)) := h7
          _ = (m₁ : ℝ) * (B.card : ℝ) * (L : ℝ) := by ring
          _ ≤ C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ) := h6
        have h9 : 0 < (M : ℝ) * (P.card : ℝ) := by positivity
        have h10 : (B.card : ℝ) / (K * (TΔ.card : ℝ)) ≤ C₁ * Real.rpow R s := by
          calc (B.card : ℝ) / (K * (TΔ.card : ℝ))
            = ((B.card : ℝ) * (M : ℝ) * (P.card : ℝ) / (K * (TΔ.card : ℝ))) / ((M : ℝ) * (P.card : ℝ)) := by field_simp [h9.ne'] <;> ring
          _ ≤ (C₁ * Real.rpow R s * (M : ℝ) * (P.card : ℝ)) / ((M : ℝ) * (P.card : ℝ)) := by gcongr
          _ = C₁ * Real.rpow R s := by field_simp [h9.ne'] <;> ring
        have h11 : (B.card : ℝ) ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := by
          have h_pos : 0 < K * (TΔ.card : ℝ) := by positivity
          have h_eq : (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ))) = (B.card : ℝ) := by
            have h_ne : (K * (TΔ.card : ℝ)) ≠ 0 := h_pos.ne'
            calc (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ)))
              = (B.card : ℝ) * ((K * (TΔ.card : ℝ)) / (K * (TΔ.card : ℝ))) := by ring
            _ = (B.card : ℝ) * 1 := by rw [div_self h_ne]
            _ = (B.card : ℝ) := by ring
          calc (B.card : ℝ)
            = (K * (TΔ.card : ℝ)) * ((B.card : ℝ) / (K * (TΔ.card : ℝ))) := h_eq.symm
          _ ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := by gcongr
        have h12 : Real.rpow R s ≤ 2 * Real.rpow r s := h_rpow
        calc (B.card : ℝ)
          ≤ (K * (TΔ.card : ℝ)) * (C₁ * Real.rpow R s) := h11
        _ ≤ (K * (TΔ.card : ℝ)) * (C₁ * (2 * Real.rpow r s)) := by gcongr
        _ = (K * 2 * C₁) * Real.rpow r s * (TΔ.card : ℝ) := by ring

      exact_mod_cast h_final

  exact ⟨hTΔ_nonempty, h_const, hs, h_sep, h_ball⟩

end InductionOnScales

end
