module

/-
# Phase 0 Composition V3 — with Pz trimming (generalized C)

Wraps `phase0_composition_v2` with `pz_trim_wrapper` to absorb the
constant blowup from trimming.

## Generalized constant contract

Given a base budget exponent `η_work` and an input constant `C` with
`1 ≤ C` and `35·C ≤ δ^{-η_work}`, V3:
- Trims Pz sets from constant `C` to `C_work = 35·C`
- Absorbs `C_work` into the Phase0 budget `δ^{-η_work}`
- Returns `η_target = η_work/2` (the small-union exponent)

The small-union budget exponent is decoupled from the absorption exponent:
- **Absorption exponent** `η = η_work`: used for `C_work ≤ δ^{-η_work}` and
  the weak size bound derivation.
- **Small-union exponent** `η_small = η_work/2`: used for `hP_small` at
  `2s + η_small`, the popularity constant `c`, and the strong size bound.

This decoupling is implemented in V2 via the separate `η_small` parameter.

Intended scaling: choose base `η0`, `c = 1/4`, then
`η_target = c·η0`, `η_work = 2c·η0 = 2·η_target`.
The input constant C is typically `δ^{-η_target}`, but V3 supports any
`C` satisfying `35·C ≤ δ^{-η_work}`.

## Whiteprint node
`phase0_composition_v3`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.ProductLikeIncidence.Phase0.PzTrimWrapper
public import MyLeanRepo.ProductLikeIncidence.Phase0.Phase0CompositionV2
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Weaken the constant of a `(δ,s,C)`-set from `C1` to `C2` when `C1 ≤ C2`. -/
lemma weaken_delta_set_constant {d : ℕ} {δ s C1 C2 : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsDeltaSCSet δ s C1 P) (hle : C1 ≤ C2) :
    IsDeltaSCSet δ s C2 P := by
  rcases h with ⟨hBdd, hNonempty, h1d, hδdyadic, hδpos, hsnonneg, hsdim, hCpos, hreg⟩
  have hC2_pos : 0 < C2 := by linarith
  refine' ⟨hBdd, hNonempty, h1d, hδdyadic, hδpos, hsnonneg, hsdim, hC2_pos, _⟩
  intro r Q hr hQ hδr hr1
  have h_old := @hreg r Q hr hQ hδr hr1
  have h_C_le : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hle
  have h_main : ENNReal.ofReal C1 * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) ≤
      ENNReal.ofReal C2 * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) := by
    gcongr
  exact le_trans h_old h_main

/-- **Trimming absorption threshold**: For `η_work > 0`, if `0 < δ ≤ 35^{-2/η_work}`,
then `35 * δ^{-η_work/2} ≤ δ^{-η_work}`. This ensures the trimmed constant
`C_work = 35 * δ^{-η_target}` fits within the Phase0 budget `δ^{-η_work}`.

Use this to prove `hC_absorb` when `C = δ^{-η_work/2}`. -/
lemma trimming_absorption_threshold_v3 (η_work : ℝ) (hη_work_pos : 0 < η_work)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ (35 : ℝ) ^ (-2 / η_work)) :
    35 * δ ^ (-(η_work / 2)) ≤ δ ^ (-η_work) := by
  have h1 : 0 < (35 : ℝ) := by norm_num
  have h2 : δ ^ (-(η_work / 2)) ≥ 35 := by
    let b : ℝ := (35 : ℝ) ^ (-2 / η_work)
    have hb_pos : 0 < b := by positivity
    have hδ_le_b : δ ≤ b := hδ_le
    have h_log_b : Real.log b = (-2 / η_work) * Real.log 35 := by
      rw [Real.log_rpow (by norm_num)]
    have h_log1 : Real.log δ ≤ Real.log b := Real.log_le_log (by positivity) hδ_le_b
    have h_goal : Real.log 35 ≤ -(η_work / 2) * Real.log δ := by
      rw [h_log_b] at h_log1
      have h : -(η_work / 2) * Real.log δ ≥ -(η_work / 2) * ((-2 / η_work) * Real.log 35) := by
        nlinarith
      have h_coeff : -(η_work / 2) * (-2 / η_work) = 1 := by
        field_simp [hη_work_pos.ne'] <;> ring
      have h2 : -(η_work / 2) * ((-2 / η_work) * Real.log 35) = Real.log 35 := by
        rw [← mul_assoc, h_coeff, one_mul]
      linarith
    have h5 : Real.log (35 : ℝ) ≤ Real.log (δ ^ (-(η_work / 2))) := by
      rw [Real.log_rpow (by positivity)]
      exact h_goal
    exact (Real.log_le_log_iff (by norm_num) (by positivity)).mp h5
  have h7 : 35 * δ ^ (-(η_work / 2)) ≤ δ ^ (-(η_work / 2)) * δ ^ (-(η_work / 2)) := by
    gcongr
  have h8 : δ ^ (-(η_work / 2)) * δ ^ (-(η_work / 2)) = δ ^ (-η_work) := by
    rw [← Real.rpow_add hδ_pos]
    <;> ring_nf
  rw [h8] at h7
  exact h7

/-- **Phase 0 Composition V3** (generalized C): trim Pz sets from constant C
to `C_work = 35*C`, then run Phase0 V2 with absorption exponent `η_work`
and small-union exponent `η_work/2`. Returns `η_target`, `C_work`, `Pz_trim`,
and the Phase0 V2 outputs. -/
lemma phase0_composition_v3
    {δ s τ η_work κ0 qBox C : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hη_work_pos : 0 < η_work)
    (hC_ge1 : 1 ≤ C)
    (hC_absorb : 35 * C ≤ δ ^ (-η_work))
    (hκ : (η_work / 2) + 4 * η_work < 2 * (s - κ0))
    (hqBox_pos : 0 < qBox)
    (hδ_pbar : δ ^ (-(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work)) ≥ 98)
    (hδ_box_small : δ ^ (-qBox) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hy_bounds : ∀ y ∈ Y, 0 ≤ y ∧ y ≤ 1)
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C (Pz z))
    (hPz_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_bounded : ∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz z))
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))))
    (h_cY_large : 2 < (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ)) :
    ∃ (η_target : ℝ)
      (C_work : ℝ)
      (Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))),
      0 < η_target ∧
      η_target = η_work / 2 ∧
      C_work = 35 * C ∧
      (∀ z ∈ productLikeIncidenceSet Y X, Pz_trim z ⊆ Pz z) ∧
      (∀ z ∈ productLikeIncidenceSet Y X, IsDeltaSCSet (d := 2) δ s C_work (Pz_trim z)) ∧
      (∀ z ∈ productLikeIncidenceSet Y X,
        ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ) ∧
      (∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz_trim z)) ∧
      (let U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
         ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y))
       let T := ⋃ y ∈ Y, U_y y
       let c := δ ^ (η_work / 2) / (7 * C_work ^ 2)
       ∃ (Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))),
         Tbar ⊆ T ∧
         IsDeltaSCSet (d := 2) δ (2 * s) (4 * (49 * C_work^4) / c^2) (⋃₀ Tbar) ∧
         ENat.toENNReal Tbar.encard ≥ ENNReal.ofReal (c / 2) * ENat.toENNReal T.encard ∧
         (∀ Q ∈ Tbar, ENat.toENNReal ({y ∈ Y | Q ∈ U_y y}).encard ≥
           ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) ∧
         (∀ p ∈ ⋃₀ Tbar,
           ENat.toENNReal ({y ∈ Y | p ∈ ⋃₀ (Tbar ∩ U_y y)}).encard ≥
             ENNReal.ofReal (c / 2) * ENat.toENNReal Y.encard) ∧
         (∀ y ∈ Y, ∀ p ∈ ⋃₀ (Tbar ∩ U_y y),
           ∃ x ∈ X y, |p 0 * y + p 1 - x| ≤ 4 * δ) ∧
         ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work ^ 4)) ≤
           ENat.toENNReal Tbar.encard ∧
         ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ ENat.toENNReal Tbar.encard ∧
         (∃ (Rpow : ℝ), (∃ (k : ℕ), Rpow = (2 : ℝ) ^ k) ∧
           (∀ p ∈ ⋃₀ Tbar, |p 0| ≤ Rpow ∧ |p 1| ≤ Rpow) ∧
           4 * Rpow ≤ δ ^ (-qBox))) := by
  let η_target : ℝ := η_work / 2
  have hη_target_pos : 0 < η_target := by
    dsimp only [η_target]
    linarith
  let C_orig : ℝ := C
  let C_work : ℝ := 35 * C_orig
  have hC_pos : 0 < C := by linarith
  have hC_orig_ge1 : 1 ≤ C_orig := hC_ge1
  have hC_work_ge1 : 1 ≤ C_work := by
    dsimp only [C_work]
    have h1 : 1 ≤ C_orig := hC_orig_ge1
    have h2 : 35 * C_orig ≥ 35 := by
      have h3 : (35 : ℝ) * C_orig ≥ (35 : ℝ) * 1 := by gcongr
      linarith
    linarith
  have hC_work_pos : 0 < C_work := by positivity
  have hC_work_le : C_work ≤ δ ^ (-η_work) := by
    dsimp only [C_work, C_orig]
    exact hC_absorb

  have hδ_le_one : δ ≤ 1 := by
    rcases hδ_dyadic with ⟨n, rfl⟩
    cases n with
    | zero => norm_num
    | succ n' => simp [zpow_neg, zpow_ofNat] <;> field_simp <;> norm_num

  let M : ℝ := C_orig⁻¹ * δ ^ (-s)
  have hM_pos : 0 < M := by positivity
  have hM_lower : C_orig⁻¹ * δ ^ (-s) ≤ M := by rfl

  have h_trim_exists : ∀ (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ productLikeIncidenceSet Y X →
      ∃ (Pz_trim : Set (EuclideanSpace ℝ (Fin 2)))
        (A' : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
        Pz_trim = (Pz z) ∩ ⋃₀ (A' : Set _) ∧
        Pz_trim ⊆ Pz z ∧
        IsDeltaSCSet δ s C_work Pz_trim ∧
        (∀ p ∈ Pz_trim, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ) ∧
        ENNReal.ofReal (M / 2) ≤ ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) ∧
        ENat.toENNReal (dyadicCoveringNumber δ Pz_trim) ≤ ENNReal.ofReal (2 * M + 1) := by
    intro z hz
    have hz1 : 0 ≤ z 1 := by
      have hzy : z 1 ∈ Y := by
        simp only [productLikeIncidenceSet, Set.mem_iUnion] at hz
        rcases hz with ⟨y, hy, hz'⟩
        have h_eq : z 1 = y := hz'.2
        rw [h_eq] <;> exact hy
      exact (hy_bounds (z 1) hzy).1
    have hz2 : z 1 ≤ 1 := by
      have hzy : z 1 ∈ Y := by
        simp only [productLikeIncidenceSet, Set.mem_iUnion] at hz
        rcases hz with ⟨y, hy, hz'⟩
        have h_eq : z 1 = y := hz'.2
        rw [h_eq] <;> exact hy
      exact (hy_bounds (z 1) hzy).2
    have hPz_delta_z : IsDeltaSCSet δ s C_orig (Pz z) := hPz_delta z hz
    have hPz_strip_z : ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ :=
      hPz_approx z hz
    have hM_le : ENNReal.ofReal M ≤ ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) :=
      covering_lower_bound hPz_delta_z
    exact pz_trim_wrapper
      (hδ := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hC_ge1 := hC_orig_ge1)
      (hM_pos := hM_pos) (hM_lower := hM_lower)
      (x := z 0) (y := z 1) (hy0 := hz1) (hy1 := hz2)
      (hPz_delta := hPz_delta_z) (hPz_strip := hPz_strip_z)
      (hM_le := hM_le)

  choose Pz_trim A' h1 h2 h3 h4 h5 h6 using h_trim_exists

  let Pz_trim' : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun z => if hz : z ∈ productLikeIncidenceSet Y X then Pz_trim z hz else ∅

  have hPz_trim_sub : ∀ z ∈ productLikeIncidenceSet Y X, Pz_trim' z ⊆ Pz z := by
    intro z hz
    simpa [Pz_trim', hz] using h2 z hz

  have hPz_trim_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C_work (Pz_trim' z) := by
    intro z hz
    simpa [Pz_trim', hz] using h3 z hz

  have hPz_trim_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz_trim' z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
    intro z hz
    simpa [Pz_trim', hz] using h4 z hz

  have hPz_trim_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz_trim' z) := by
    intro z hz
    have h_sub : Pz_trim' z ⊆ Pz z := hPz_trim_sub z hz
    exact (hPz_bounded z hz).subset h_sub

  have h_size_bound_trim : ∀ z ∈ productLikeIncidenceSet Y X,
      ENat.toENNReal (dyadicCoveringNumber δ (Pz_trim' z)) ≤
        ENNReal.ofReal (C_work * δ ^ (-s)) := by
    intro z hz
    have h_upper : ENat.toENNReal (dyadicCoveringNumber δ (Pz_trim' z)) ≤
        ENNReal.ofReal (2 * M + 1) := by
      simpa [Pz_trim', hz] using h6 z hz
    have h1 : 1 ≤ δ ^ (-s) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos hδ_le_one (by linarith)
    have h_pos_s : 0 < δ ^ (-s) := by positivity
    have hC_pos' : 0 < C_orig := by linarith
    have h_inv_le : C_orig⁻¹ ≤ 1 := by
      have h : C_orig ≥ 1 := hC_orig_ge1
      have h' : (1 : ℝ) / C_orig ≤ 1 := by
        apply (div_le_one hC_pos').mpr
        linarith
      have h_eq : C_orig⁻¹ = (1 : ℝ) / C_orig := by
        exact inv_eq_one_div C_orig
      rw [h_eq]
      exact h'
    have h_real : 2 * M + 1 ≤ C_work * δ ^ (-s) := by
      dsimp only [M, C_work, C_orig]
      have h2 : 2 * C⁻¹ * δ ^ (-s) ≤ 2 * δ ^ (-s) := by
        gcongr
        <;> linarith
      have h3 : (1 : ℝ) ≤ δ ^ (-s) := h1
      have h4 : 2 * δ ^ (-s) + 1 ≤ 3 * δ ^ (-s) := by
        have h5 : 1 ≤ δ ^ (-s) := h3
        linarith
      have h6 : 3 * δ ^ (-s) ≤ 35 * C * δ ^ (-s) := by
        have h7 : 3 ≤ 35 * C := by linarith
        gcongr
        <;> linarith
      linarith
    have h_ennreal : ENNReal.ofReal (2 * M + 1) ≤ ENNReal.ofReal (C_work * δ ^ (-s)) := by
      exact ENNReal.ofReal_le_ofReal h_real
    exact le_trans h_upper h_ennreal

  have hP_small_trim : ENat.toENNReal (dyadicCoveringNumber δ
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz_trim' z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))) := by
    have h_union_sub : (⋃ z ∈ productLikeIncidenceSet Y X, Pz_trim' z) ⊆
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) := by
      apply Set.biUnion_mono (Set.Subset.refl _)
      intro z hz
      exact hPz_trim_sub z hz
    have h_mono : ENat.toENNReal (dyadicCoveringNumber δ
          (⋃ z ∈ productLikeIncidenceSet Y X, Pz_trim' z)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ
          (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) :=
      coveringNumber_mono h_union_sub
    exact lt_of_le_of_lt h_mono hP_small

  have hs_le_one : s ≤ 1 := by linarith

  have hC_orig_le_work : C_orig ≤ C_work := by
    dsimp only [C_work]
    have h : 1 ≤ 35 := by norm_num
    have h2 : C_orig ≤ 35 * C_orig := by linarith
    exact h2

  have hY_delta_work : IsProductLikeRealDeltaSCSet δ τ C_work Y := by
    have h' : IsDeltaSCSet δ τ C_orig (realLineCopy Y) := hY_delta
    exact weaken_delta_set_constant h' hC_orig_le_work

  have hXy_delta_work : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C_work (X y) := by
    intro y hy
    have h1 := hXy_delta y hy
    have h2 : IsDeltaSCSet δ s C_orig (realLineCopy (X y)) := h1.2
    exact ⟨h1.1, weaken_delta_set_constant h2 hC_orig_le_work⟩

  exact ⟨η_target, C_work, Pz_trim', hη_target_pos, rfl, rfl, hPz_trim_sub,
    hPz_trim_delta, hPz_trim_approx, hPz_trim_bounded,
    phase0_composition_v2
      (η := η_work) (η_small := η_work / 2)
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic)
      (hs_pos := hs_pos) (hs_le_one := hs_le_one)
      (hC_ge1 := hC_work_ge1) (hC_pos := hC_work_pos)
      (hη_work_pos) (hη_small_pos := by linarith) (hC_le := hC_work_le)
      (hκ) (hδ_pbar := hδ_pbar)
      (hτ_pos := hτ_pos) (hqBox_pos := hqBox_pos)
      (hδ_box_small := hδ_box_small)
      (hY_fin := hY_fin) (hY_nonempty := hY_nonempty)
      (hY_sub) (hY_delta_work)
      (hXy_delta_work) (hy_bounds)
      (hPz_trim_delta) (hPz_trim_approx) (hPz_trim_bounded)
      (h_size_bound_trim) (hP_small_trim) (h_cY_large)⟩

end ProductLikeIncidence.ProductReduction
