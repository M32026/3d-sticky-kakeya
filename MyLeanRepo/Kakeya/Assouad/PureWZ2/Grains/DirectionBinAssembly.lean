import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionBinRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.EasyRegimeAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BoundedIntervalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfig
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import Mathlib.Tactic

/-!
# Direction bin assembly for outputLoss > 1

Constructs a `PureWZ2GrainConfiguration` for `outputLoss > 1` by restricting
the shading to a narrow direction bin of width `δ` while keeping the full
family for CWA.

## Key idea

1. Use base config at `loss_src < outputLoss - 1` (weaker density, smaller CWA constant).
2. Pigeonhole tube directions into angular bins of width `δ`.
3. Select a bin with ≥ 1/N of total shading mass (N ≤ (2π+1)/δ).
4. The ε = outputLoss - 1 - loss_src slack absorbs the 2π+1 factor:
   S_bin ≥ δ^(loss_src+1)/(2π+1) · B_full ≥ δ^outputLoss · B_full.
5. CWA stays on the full family (no transfer needed).
6. Constant planeMap `binPerpVector(θ_center)`: incidence ≤ (√3/2)·δ < δ.
7. Local AD: easy regime (`outputLoss > 1 > σ/2`).
8. Global AD: Case 1 bounded interval (`outputLoss > 1 > σ`).

## Whiteprint node

`PureWZ2/Grains/DirectionBinAssembly`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set ENNReal MeasureTheory Finset

attribute [local instance] Classical.propDecidable

/-!
## Density pigeonhole
-/

/-- Density pigeonhole: given a partition of items into bins and a global density
bound `λ * ∑ bodyWeight ≤ ∑ shadingWeight`, there exists a bin with positive
body weight and the same density bound. -/
lemma density_pigeonhole
    {n N : ℕ}
    (bodyWeight shadingWeight : Fin n → ENNReal)
    (color : Fin n → Fin N)
    (lambda : ENNReal)
    (h_lambda_pos : 0 < lambda)
    (h_sub : ∀ i, shadingWeight i ≤ bodyWeight i)
    (h_all_finite : ∀ i, bodyWeight i ≠ ⊤)
    (h_shading_finite : ∀ i, shadingWeight i ≠ ⊤)
    (h_total_body_pos : 0 < ∑ i, bodyWeight i)
    (h_dense : lambda * ∑ i, bodyWeight i ≤ ∑ i, shadingWeight i) :
    ∃ k : Fin N,
      (0 < ∑ i ∈ (univ.filter fun i => color i = k), bodyWeight i) ∧
      lambda * ∑ i ∈ (univ.filter fun i => color i = k), bodyWeight i ≤
        ∑ i ∈ (univ.filter fun i => color i = k), shadingWeight i := by
  let bin (k : Fin N) : Finset (Fin n) := Finset.univ.filter fun i => color i = k
  let B (k : Fin N) : ENNReal := ∑ i ∈ bin k, bodyWeight i
  let S (k : Fin N) : ENNReal := ∑ i ∈ bin k, shadingWeight i

  have hB_sum : ∑ k : Fin N, B k = ∑ i : Fin n, bodyWeight i := by
    simp [B, bin, Finset.sum_filter, Finset.sum_comm]
  have hS_sum : ∑ k : Fin N, S k = ∑ i : Fin n, shadingWeight i := by
    simp [S, bin, Finset.sum_filter, Finset.sum_comm]

  by_cases h : ∃ k : Fin N, (0 < B k) ∧ (lambda * B k ≤ S k)
  · rcases h with ⟨k, hB_pos, h_le⟩
    exact ⟨k, hB_pos, h_le⟩
  · have h' : ∀ k : Fin N, ¬(0 < B k ∧ lambda * B k ≤ S k) := by simpa using h
    have h'' : ∀ k : Fin N, B k = 0 ∨ S k < lambda * B k := by
      intro k
      have h1 : ¬(0 < B k ∧ lambda * B k ≤ S k) := h' k
      by_cases hB : 0 < B k
      · have h2 : ¬(lambda * B k ≤ S k) := by tauto
        exact Or.inr (not_le.mp h2)
      · have hB0 : B k = 0 := by simpa using hB
        exact Or.inl hB0

    let K : Finset (Fin N) := Finset.univ.filter fun k => 0 < B k

    have hK_nonempty : K.Nonempty := by
      by_contra hK
      have hK_empty : K = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hK
      have h_all_zero : ∀ k : Fin N, B k = 0 := by
        intro k
        have h3 : k ∉ K := by rw [hK_empty]; simp
        have h4 : ¬(0 < B k) := by
          simpa [K, Finset.mem_filter, Finset.mem_univ] using h3
        have h5 : B k ≤ 0 := not_lt.mp h4
        simpa using h5
      have h4 : ∑ k : Fin N, B k = 0 := by
        rw [Finset.sum_congr rfl (fun k _ => h_all_zero k)] <;> simp
      rw [hB_sum] at h4
      have h5 : (0 : ENNReal) < ∑ i : Fin n, bodyWeight i := h_total_body_pos
      rw [h4] at h5
      simpa using h5

    have h_strict : ∀ k ∈ K, S k < lambda * B k := by
      intro k hk
      have hB_pos : 0 < B k := by
        simpa [K, Finset.mem_filter, Finset.mem_univ] using hk
      rcases h'' k with (hB0 | h_lt)
      · rw [hB0] at hB_pos; simpa using hB_pos
      · exact h_lt

    have h_S0 : ∀ k ∉ K, S k = 0 := by
      intro k hk
      have h4 : ¬(0 < B k) := by
        simpa [K, Finset.mem_filter, Finset.mem_univ] using hk
      have h5 : B k ≤ 0 := not_lt.mp h4
      have hB0 : B k = 0 := by simpa using h5
      have h_body0 : ∀ i ∈ bin k, bodyWeight i = 0 := by
        intro i hi
        have h_sum0 : B k = 0 := hB0
        simp only [B] at h_sum0
        have h_all : ∀ i ∈ bin k, bodyWeight i = 0 := by
          rwa [Finset.sum_eq_zero_iff] at h_sum0
        exact h_all i hi
      have h_shad0 : ∀ i ∈ bin k, shadingWeight i = 0 := by
        intro i hi
        have h_body : bodyWeight i = 0 := h_body0 i hi
        have h_le : shadingWeight i ≤ bodyWeight i := h_sub i
        rw [h_body] at h_le
        simpa using h_le
      simp only [S]
      rw [Finset.sum_congr rfl h_shad0] <;> simp

    have h_B0 : ∀ k ∉ K, B k = 0 := by
      intro k hk
      have h4 : ¬(0 < B k) := by
        simpa [K, Finset.mem_filter, Finset.mem_univ] using hk
      have h5 : B k ≤ 0 := not_lt.mp h4
      simpa using h5

    have h_sum_S : ∑ k : Fin N, S k = ∑ k ∈ K, S k := by
      exact (Finset.sum_subset (Finset.subset_univ K) (fun k _ hk => h_S0 k hk)).symm

    have h_sum_B : ∑ k : Fin N, B k = ∑ k ∈ K, B k := by
      exact (Finset.sum_subset (Finset.subset_univ K) (fun k _ hk => h_B0 k hk)).symm

    have h_sum_lambdaB : ∑ k : Fin N, lambda * B k = ∑ k ∈ K, lambda * B k := by
      calc ∑ k : Fin N, lambda * B k
          = lambda * ∑ k : Fin N, B k := by rw [Finset.mul_sum]
        _ = lambda * ∑ k ∈ K, B k := by rw [h_sum_B]
        _ = ∑ k ∈ K, lambda * B k := by rw [Finset.mul_sum]

    have h_sum_lt : ∑ k ∈ K, S k < ∑ k ∈ K, lambda * B k :=
      ENNReal.sum_lt_sum_of_nonempty hK_nonempty h_strict

    have h_dense' : lambda * ∑ k : Fin N, B k ≤ ∑ k : Fin N, S k := by
      have h : lambda * ∑ i : Fin n, bodyWeight i ≤ ∑ i : Fin n, shadingWeight i := h_dense
      rw [← hB_sum, ← hS_sum] at h
      exact h
    have h2 : lambda * ∑ k : Fin N, B k = ∑ k ∈ K, lambda * B k := by
      calc lambda * ∑ k : Fin N, B k
          = ∑ k : Fin N, lambda * B k := by rw [Finset.mul_sum]
        _ = ∑ k ∈ K, lambda * B k := h_sum_lambdaB
    have h_contra : ∑ k : Fin N, S k < lambda * ∑ k : Fin N, B k := by
      rw [h_sum_S, h2]
      exact h_sum_lt
    have h_circ : ∑ k : Fin N, S k < ∑ k : Fin N, S k :=
      lt_of_lt_of_le h_contra h_dense'
    exact False.elim (lt_irrefl _ h_circ)

/-!
## Direction bin assembly
-/

/-- Direction bin assembly for outputLoss > 1.

Given a base config at `loss_src < outputLoss - 1` (with ε = outputLoss - 1 - loss_src > 0
small enough that `(2π+1) * δ^ε ≤ 1`), produces a grain configuration at `outputLoss` by
restricting the shading to a direction bin of width `δ` while keeping the full
family for CWA.

The ε slack absorbs the `2π+1` factor from the bin pigeonhole:
- Best bin has ≥ 1/N of shading mass, N ≤ (2π+1)/δ
- So S_bin ≥ δ^(loss_src+1)/(2π+1) · B_full = δ^(outputLoss-ε)/(2π+1) · B_full
- With (2π+1)·δ^ε ≤ 1, this gives S_bin ≥ δ^outputLoss · B_full ✓ -/
theorem direction_bin_grain_config
    {sigma outputLoss delta loss_src : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (houtputLoss_gt_one : 1 < outputLoss)
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (hloss_src_lt : loss_src < outputLoss - 1)
    (h_absorb : (2 * Real.pi + 1) * delta^(outputLoss - 1 - loss_src) ≤ 1)
    (hsmall_global : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma))
    (line_class : WZ1PaperIsLineClass family)
    (cubical : WZ1PaperIsCubicalShading shading)
    (extremal_src : WZ2PaperCroppedIsExtremal sigma loss_src family shading)
    (top_cwa_src : WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-loss_src))) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta) := by
  set epsilon : ℝ := outputLoss - 1 - loss_src with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by linarith

  -- Derive easy-regime smallness from stronger global smallness
  have hsmall_easy : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma / 2) := by
    have h_base : 1 ≤ 1 / delta := by
      apply one_le_one_div <;> linarith
    have h2 : (1 / delta)^(outputLoss - sigma) ≤ (1 / delta)^(outputLoss - sigma / 2) :=
      Real.rpow_le_rpow_of_exponent_le h_base (by linarith)
    exact hsmall_global.trans h2

  -- Number of direction bins
  let N : ℕ := Nat.ceil (2 * Real.pi / delta)
  have hN_pos : 0 < N := by
    apply Nat.ceil_pos.mpr
    positivity
  have hN_le : (N : ℝ) ≤ (2 * Real.pi + 1) / delta := by
    have h1 : (N : ℝ) < 2 * Real.pi / delta + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1' : (N : ℝ) ≤ 2 * Real.pi / delta + 1 := le_of_lt h1
    have h2 : (1 : ℝ) ≤ 1 / delta := by
      apply one_le_one_div <;> linarith
    calc (N : ℝ)
      ≤ 2 * Real.pi / delta + 1 := h1'
    _ ≤ 2 * Real.pi / delta + 1 / delta := by gcongr
    _ = (2 * Real.pi + 1) / delta := by
      field_simp [hdelta_pos.ne'] <;> ring

  -- Direction bin coloring
  let color (i : Fin family.card) : Fin N :=
    ⟨Nat.floor (horizontalAngle (family.tube i).direction / delta), by
      have h_angle_nonneg : 0 ≤ horizontalAngle (family.tube i).direction :=
        (horizontalAngle_range (family.tube i).direction_unit).1
      have h_nonneg : 0 ≤ horizontalAngle (family.tube i).direction / delta := by positivity
      have h1 : horizontalAngle (family.tube i).direction < 2 * Real.pi :=
        (horizontalAngle_range (family.tube i).direction_unit).2
      have h2pi_nonneg : 0 ≤ 2 * Real.pi / delta := by positivity
      have h2 : (Nat.floor (horizontalAngle (family.tube i).direction / delta) : ℝ) < (N : ℝ) := by
        have h_le1 : (Nat.floor (horizontalAngle (family.tube i).direction / delta) : ℝ) ≤ horizontalAngle (family.tube i).direction / delta :=
          Nat.floor_le h_nonneg
        have h_le2 : 2 * Real.pi / delta ≤ (N : ℝ) := Nat.le_ceil (2 * Real.pi / delta)
        calc (Nat.floor (horizontalAngle (family.tube i).direction / delta) : ℝ)
          ≤ horizontalAngle (family.tube i).direction / delta := h_le1
        _ < 2 * Real.pi / delta := by gcongr
        _ ≤ (N : ℝ) := h_le2
      exact_mod_cast h2⟩

  let bin (k : Fin N) : Finset (Fin family.card) :=
    Finset.univ.filter fun i => color i = k

  -- Mass pigeonhole: select bin with ≥ 1/N of total shading mass
  let S_bin (k : Fin N) : ENNReal := ∑ i ∈ bin k, volume (shading.carrier i)
  have h_mass_def : shading.mass = ∑ i, volume (shading.carrier i) := by
    simp [Streamlined.Shading.mass]
  have h_sum : ∑ k : Fin N, S_bin k = shading.mass := by
    rw [h_mass_def]
    have h : ∑ k : Fin N, S_bin k = ∑ i : Fin family.card, volume (shading.carrier i) := by
      simp [S_bin, bin, Finset.sum_filter, Finset.sum_comm]
      <;> rfl
    exact h
  have hN_ne_zero : (N : ENNReal) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hN_ne_top : (N : ENNReal) ≠ ⊤ := by simp
  have h_cancel : (N : ENNReal) * ((1 : ENNReal) / N) = 1 :=
    ENNReal.mul_div_cancel hN_ne_zero hN_ne_top
  have h_exists_bin : ∃ (k : Fin N), S_bin k ≥ (1 : ENNReal) / N * shading.mass := by
    let weight : Fin family.card → ENNReal := fun i => volume (shading.carrier i)
    rcases weighted_pigeonhole_simple hN_pos weight color with ⟨k, hk⟩
    refine' ⟨k, _⟩
    have h1 : (∑ i, weight i) ≤ (N : ENNReal) * S_bin k := hk
    have h2 : (1 : ENNReal) / N * (∑ i, weight i) ≤ S_bin k := by
      have h3 : (1 : ENNReal) / N = (N : ENNReal)⁻¹ := by
        simp [div_eq_mul_inv]
      rw [h3]
      have h4 : (N : ENNReal)⁻¹ * (∑ i, weight i) ≤
          (N : ENNReal)⁻¹ * ((N : ENNReal) * S_bin k) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : (N : ENNReal)⁻¹ * ((N : ENNReal) * S_bin k) = S_bin k := by
        have h51 : (N : ENNReal)⁻¹ * (N : ENNReal) = 1 := ENNReal.inv_mul_cancel hN_ne_zero hN_ne_top
        calc
          (N : ENNReal)⁻¹ * ((N : ENNReal) * S_bin k)
            = ((N : ENNReal)⁻¹ * (N : ENNReal)) * S_bin k := by rw [mul_assoc]
          _ = 1 * S_bin k := by rw [h51]
          _ = S_bin k := by rw [one_mul]
      rw [h5] at h4
      exact h4
    have h6 : (∑ i, weight i) = shading.mass := by
      have h7 : (∑ i, weight i) = ∑ i, volume (shading.carrier i) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      rw [h7]
      exact h_mass_def.symm
    rw [h6] at h2
    exact h2

  rcases h_exists_bin with ⟨k, hbin_mass⟩

  -- Define bin shading on the FULL family (empty carriers outside bin)
  let binShading : WZ1PaperTubeShading family :=
    { carrier := fun i => if i ∈ bin k then shading.carrier i else ∅
      measurable_carrier := fun i => by
        by_cases h : i ∈ bin k
        · rw [if_pos h]; exact shading.measurable_carrier i
        · rw [if_neg h]; exact MeasurableSet.empty
      subset_body := by
        intro i x hx
        by_cases h : i ∈ bin k
        · rw [if_pos h] at hx
          exact shading.subset_body i hx
        · rw [if_neg h] at hx
          simpa using hx }

  -- Bin shading mass equals sum over selected bin
  have h_bin_mass_eq : binShading.mass = S_bin k := by
    have h1 : binShading.mass = ∑ i, volume (binShading.carrier i) := by
      simp [Streamlined.Shading.mass]
    rw [h1]
    have h_zero : ∀ (i : Fin family.card), i ∉ bin k → volume (binShading.carrier i) = 0 := by
      intro i hni
      have hcar : binShading.carrier i = ∅ := by
        have hif : binShading.carrier i = (if i ∈ bin k then shading.carrier i else ∅) := by rfl
        rw [hif, if_neg hni]
      rw [hcar]
      exact MeasureTheory.measure_empty
    have h_sub : bin k ⊆ (Finset.univ : Finset (Fin family.card)) := by simp
    have h_eq : ∑ i ∈ bin k, volume (binShading.carrier i) = ∑ i, volume (binShading.carrier i) :=
      Finset.sum_subset h_sub (fun i _ hni => h_zero i hni)
    have h2 : ∑ i, volume (binShading.carrier i) = ∑ i ∈ bin k, volume (binShading.carrier i) :=
      h_eq.symm
    rw [h2]
    have h4 : ∀ i ∈ bin k, volume (binShading.carrier i) = volume (shading.carrier i) := by
      intro i hi
      have hcar : binShading.carrier i = shading.carrier i := by
        have hif : binShading.carrier i = (if i ∈ bin k then shading.carrier i else ∅) := by rfl
        rw [hif, if_pos hi]
      rw [hcar]
    have h5 : ∑ i ∈ bin k, volume (binShading.carrier i) = ∑ i ∈ bin k, volume (shading.carrier i) :=
      Finset.sum_congr rfl h4
    rw [h5]
    <;> rfl

  -- Constant inequality: N * δ^outputLoss ≤ δ^loss_src (in ℝ)
  have h_const_real : (N : ℝ) * delta ^ outputLoss ≤ delta ^ loss_src := by
    have h_exp1 : delta ^ outputLoss = delta ^ (outputLoss - 1) * delta := by
      have h : delta ^ outputLoss = delta ^ ((outputLoss - 1) + (1 : ℝ)) := by ring_nf
      rw [h, Real.rpow_add hdelta_pos]
      <;> simp
    have h1 : (N : ℝ) * delta ^ outputLoss ≤ (2 * Real.pi + 1) * delta ^ (outputLoss - 1) := by
      calc (N : ℝ) * delta ^ outputLoss
        ≤ ((2 * Real.pi + 1) / delta) * delta ^ outputLoss := by gcongr
      _ = (2 * Real.pi + 1) * delta ^ (outputLoss - 1) := by
        rw [h_exp1]
        field_simp [hdelta_pos.ne'] <;> ring
    have h_exp2 : delta ^ (outputLoss - 1) = delta ^ (outputLoss - 1 - loss_src) * delta ^ loss_src := by
      have h : delta ^ (outputLoss - 1) = delta ^ ((outputLoss - 1 - loss_src) + loss_src) := by ring_nf
      rw [h, Real.rpow_add hdelta_pos]
    have h2 : (2 * Real.pi + 1) * delta ^ (outputLoss - 1) ≤ delta ^ loss_src := by
      rw [h_exp2]
      have h3 : (2 * Real.pi + 1) * delta ^ (outputLoss - 1 - loss_src) ≤ 1 := h_absorb
      have h4 : 0 ≤ delta ^ loss_src := by positivity
      nlinarith
    exact h1.trans h2

  -- Lift to ENNReal
  have h_const_ennreal : (N : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta loss_src := by
    simp only [Kakeya.realRpowENN]
    have h_pos1 : 0 ≤ (N : ℝ) := by positivity
    have h_pos2 : 0 ≤ delta ^ outputLoss := by positivity
    have h : ENNReal.ofReal ((N : ℝ) * delta ^ outputLoss) ≤ ENNReal.ofReal (delta ^ loss_src) :=
      ENNReal.ofReal_le_ofReal h_const_real
    have h2 : ENNReal.ofReal ((N : ℝ) * delta ^ outputLoss) =
        ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (delta ^ outputLoss) :=
      ENNReal.ofReal_mul h_pos1
    have h3 : ENNReal.ofReal (N : ℝ) = (N : ENNReal) := by norm_cast
    rw [h2, h3] at h
    exact h

  -- Dense condition: δ^outputLoss · B_full ≤ binShading.mass
  let B : ENNReal := (wz1PaperBodyFamily family).mass
  have h_const2 : Kakeya.realRpowENN delta outputLoss ≤
      (1 : ENNReal) / N * Kakeya.realRpowENN delta loss_src := by
    calc Kakeya.realRpowENN delta outputLoss
      = 1 * Kakeya.realRpowENN delta outputLoss := by simp
    _ = ((N : ENNReal) * ((1 : ENNReal) / N)) * Kakeya.realRpowENN delta outputLoss := by
      rw [h_cancel]
    _ = (1 : ENNReal) / N * ((N : ENNReal) * Kakeya.realRpowENN delta outputLoss) := by ring
    _ ≤ (1 : ENNReal) / N * Kakeya.realRpowENN delta loss_src := by gcongr
  have h_dense1 : Kakeya.realRpowENN delta outputLoss * B ≤
      (1 : ENNReal) / N * Kakeya.realRpowENN delta loss_src * B := by gcongr
  have h_dense_src : Kakeya.realRpowENN delta loss_src * B ≤ shading.mass := extremal_src.dense
  have h_dense2 : (1 : ENNReal) / N * Kakeya.realRpowENN delta loss_src * B ≤
      (1 : ENNReal) / N * shading.mass := by
    have h_comm : (1 : ENNReal) / N * Kakeya.realRpowENN delta loss_src * B =
        (1 : ENNReal) / N * (Kakeya.realRpowENN delta loss_src * B) := by ring
    rw [h_comm]
    gcongr
  have h_dense3 : (1 : ENNReal) / N * shading.mass ≤ binShading.mass := by
    rw [h_bin_mass_eq]
    exact hbin_mass
  have h_dense_output : Kakeya.realRpowENN delta outputLoss * B ≤ binShading.mass :=
    h_dense1.trans (h_dense2.trans h_dense3)

  -- Volume upper bound
  have h_sub_union : binShading.union ⊆ shading.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    have h4 : x ∈ shading.carrier i := by
      by_cases h : i ∈ bin k
      · have hcar : binShading.carrier i = shading.carrier i := by simp [binShading, h]
        rw [hcar] at hi; exact hi
      · have hcar : binShading.carrier i = ∅ := by simp [binShading, h]
        rw [hcar] at hi; simpa using hi
    exact ⟨i, h4⟩
  have h_vol_upper : volume binShading.union ≤
      Kakeya.realRpowENN delta (sigma - outputLoss) := by
    have h1 : volume binShading.union ≤ volume shading.union := measure_mono h_sub_union
    have h2 : volume shading.union ≤ Kakeya.realRpowENN delta (sigma - loss_src) :=
      extremal_src.volume_upper
    have h3 : Kakeya.realRpowENN delta (sigma - loss_src) ≤
        Kakeya.realRpowENN delta (sigma - outputLoss) := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_le_ofReal
      have h_exp : sigma - outputLoss ≤ sigma - loss_src := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le h_exp
    exact h1.trans (h2.trans h3)

  -- Cubical shading
  have h_bin_cubical : WZ1PaperIsCubicalShading binShading := by
    intro index point hp
    by_cases h : index ∈ bin k
    · have h' : point ∈ shading.carrier index := by
        simpa [binShading, h] using hp
      have hcube := cubical index point h'
      simpa [binShading, h] using hcube
    · simp [binShading, h] at hp

  have h_nonempty : family.Nonempty := extremal_src.nonempty

  -- CWA constant weakening
  have hC1_le_C2 : Kakeya.realRpowENN delta (-loss_src) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : -outputLoss ≤ -loss_src := by linarith
    have h2 : Real.rpow delta (-loss_src) ≤ Real.rpow delta (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le h_exp
    exact ENNReal.ofReal_le_ofReal h2
  have hC2_finite : WZ2PaperFiniteErrorConstant (Kakeya.realRpowENN delta (-outputLoss)) := by
    have h7 : 1 ≤ Kakeya.realRpowENN delta (-outputLoss) := by
      simp only [Kakeya.realRpowENN]
      have h8 : Real.rpow delta (-outputLoss) ≥ 1 := by
        have h10 : Real.rpow delta 0 ≤ Real.rpow delta (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le (by linarith)
        simpa using h10
      simpa [ENNReal.ofReal] using h8
    have h9 : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ⟨h7, h9⟩

  -- Weaken extremal and CWA
  have extremal_output : WZ2PaperCroppedIsExtremal sigma outputLoss family binShading := by
    refine' {
      delta_pos := hdelta_pos,
      delta_le_one := hdelta_lt_one.le,
      nonempty := h_nonempty,
      cwa_nearby_scales := weaken_cwa_nearby_scales extremal_src.cwa_nearby_scales hC1_le_C2 hC2_finite,
      cubical := h_bin_cubical,
      dense := h_dense_output,
      volume_upper := h_vol_upper
    }
  have cwa_output : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    weaken_convex_wolff_bound top_cwa_src hC1_le_C2

  -- Constant plane map vector
  let theta : ℝ := (k : ℝ) * delta
  let v : Point3 := binPerpVector theta
  have hv_norm : ‖v‖ = 1 := binPerpVector_norm theta

  -- Incidence bound
  have h_incidence : ∀ (index : Fin family.card) (point : Point3),
      ∀ (hpoint : point ∈ binShading.carrier index),
        |inner ℝ (family.tube index).direction v| ≤ delta := by
    intro index point hpoint
    have h_in_bin : index ∈ bin k := by
      by_cases h : index ∈ bin k
      · exact h
      · have hcar : binShading.carrier index = ∅ := by
          have hif : binShading.carrier index = (if index ∈ bin k then shading.carrier index else ∅) := by
            exact rfl
          rw [hif, if_neg h] <;> rfl
        rw [hcar] at hpoint
        simp at hpoint
    have h_color : color index = k := by
      simpa [bin, Finset.mem_filter, Finset.mem_univ] using h_in_bin
    have h_floor : Nat.floor (horizontalAngle (family.tube index).direction / delta) = (k : ℕ) := by
      exact congr_arg Fin.val h_color
    have h_nonneg2 : 0 ≤ horizontalAngle (family.tube index).direction / delta := by
      have h : 0 ≤ horizontalAngle (family.tube index).direction :=
        (horizontalAngle_range (family.tube index).direction_unit).1
      exact div_nonneg h (by positivity)
    have h1 : (k : ℝ) ≤ horizontalAngle (family.tube index).direction / delta := by
      rw [← h_floor]; exact Nat.floor_le h_nonneg2
    have h2 : horizontalAngle (family.tube index).direction / delta < (k + 1 : ℝ) := by
      rw [← h_floor]; exact Nat.lt_floor_add_one _
    have h_eq1 : (horizontalAngle (family.tube index).direction / delta) * delta = horizontalAngle (family.tube index).direction := by
      field_simp [hdelta_pos.ne'] <;> ring
    have h1' : (k : ℝ) * delta ≤ horizontalAngle (family.tube index).direction := by
      have h : (k : ℝ) * delta ≤ (horizontalAngle (family.tube index).direction / delta) * delta :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      rw [h_eq1] at h
      exact h
    have h_eq2 : (horizontalAngle (family.tube index).direction / delta) * delta = horizontalAngle (family.tube index).direction := by
      field_simp [hdelta_pos.ne'] <;> ring
    have h2' : horizontalAngle (family.tube index).direction < (k + 1 : ℝ) * delta := by
      have h : (horizontalAngle (family.tube index).direction / delta) * delta < ((k + 1 : ℝ)) * delta :=
        mul_lt_mul_of_pos_right h2 hdelta_pos
      rw [h_eq2] at h
      exact h
    have h_angle_in_bin : (k : ℝ) * delta ≤ horizontalAngle (family.tube index).direction ∧
        horizontalAngle (family.tube index).direction < (k + 1 : ℝ) * delta :=
      ⟨h1', h2'⟩
    have h_bound : |inner ℝ (family.tube index).direction v| ≤
        (Real.sqrt 3 / 2 : ℝ) * |horizontalAngle (family.tube index).direction - theta| :=
      direction_incidence_bound_abs (family.tube index).direction_unit (line_class index).vertical (θ := theta)
    have h_angle_diff : |horizontalAngle (family.tube index).direction - theta| < delta := by
      rcases h_angle_in_bin with ⟨ha1, ha2⟩
      have h3 : -delta < horizontalAngle (family.tube index).direction - theta := by
        have h_nonneg : 0 ≤ horizontalAngle (family.tube index).direction - theta := by linarith
        linarith [hdelta_pos]
      have h4 : horizontalAngle (family.tube index).direction - theta < delta := by linarith
      exact abs_lt.mpr ⟨h3, h4⟩
    have h_lt : |inner ℝ (family.tube index).direction v| < delta := by
      calc |inner ℝ (family.tube index).direction v|
        ≤ (Real.sqrt 3 / 2 : ℝ) * |horizontalAngle (family.tube index).direction - theta| := h_bound
      _ < (Real.sqrt 3 / 2 : ℝ) * delta :=
        mul_lt_mul_of_pos_left h_angle_diff (by positivity)
      _ ≤ delta := by
        have h5 : Real.sqrt 3 / 2 ≤ 1 := by
          have h6 : Real.sqrt 3 ≤ 2 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          linarith
        nlinarith
    exact le_of_lt h_lt

  -- Local AD (easy regime): constant plane map
  have localGrains : PureWZ2LocalGrainData binShading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) := by
    let planeMap : {point : Point3 // point ∈ binShading.union} → Point3 := fun _ => v
    have h_planeMap_lip : LipschitzWith 1 planeMap := by
      intro x y
      simp [planeMap, dist_eq_norm, hv_norm] <;> norm_num
    have h_planeMap_unit : ∀ point, ‖planeMap point‖ = 1 := by
      intro point
      simp [planeMap, hv_norm]
    have h_planeMap_incidence : ∀ index point, ∀ hpoint,
        |inner ℝ (family.tube index).direction (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta := by
      intro index point hpoint
      simpa [planeMap] using h_incidence index point hpoint
    have h_local_ad : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
        ∀ point : {point : Point3 // point ∈ binShading.union},
          PureWZ2PaperADSet1
            (scalarProjection (planeMap point)
              (binShading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
            rho (1 - sigma) (Kakeya.realRpowENN delta (-outputLoss)) := by
      intro rho hrho_ge hrho_le point
      set center : ℝ := inner ℝ v (point : Point3) with hcenter_def
      have hrho_pos : 0 < rho := by linarith
      have hE_contained : scalarProjection v
          (binShading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho))
          ⊆ Set.Icc (center - Real.sqrt rho) (center + Real.sqrt rho) := by
        intro y hy
        rcases (mem_image _ _ _).mp hy with ⟨x, hx, rfl⟩
        have hx_in_ball : x ∈ Metric.closedBall (point : Point3) (Real.sqrt rho) := hx.2
        have h_dist : dist x (point : Point3) ≤ Real.sqrt rho := hx_in_ball
        have h_inner_diff : |inner ℝ v x - center| ≤ Real.sqrt rho := by
          have h_eq : inner ℝ v x - center = inner ℝ v (x - (point : Point3)) := by
            have hcenter : center = inner ℝ v (point : Point3) := by simp [hcenter_def]
            calc inner ℝ v x - center
              = inner ℝ v x - inner ℝ v (point : Point3) := by rw [hcenter]
            _ = inner ℝ v (x - (point : Point3)) := by rw [inner_sub_right]
          rw [h_eq]
          have h5 : |inner ℝ v (x - (point : Point3))| ≤ ‖v‖ * ‖x - (point : Point3)‖ :=
            abs_real_inner_le_norm (F := Point3) v (x - (point : Point3))
          rw [hv_norm] at h5
          have h6 : ‖x - (point : Point3)‖ = dist x (point : Point3) := by
            simp [dist_eq_norm]
          rw [h6] at h5
          have h5' : |inner ℝ v (x - (point : Point3))| ≤ dist x (point : Point3) := by
            simpa [one_mul] using h5
          exact h5'.trans h_dist
        have hsymm : inner ℝ x v = inner ℝ v x := by
          exact real_inner_comm v x
        rw [hsymm]
        exact ⟨by linarith [abs_le.mp h_inner_diff], by linarith [abs_le.mp h_inner_diff]⟩
      have h_half : sigma / 2 < outputLoss := by linarith
      exact PureWZ2.easy_regime_ad
        (hC_eq := rfl) hsigma_pos hsigma_lt_one hdelta_pos hdelta_lt_one.le
        (by linarith) hrho_pos hrho_ge hsmall_easy h_half center hE_contained
    exact ⟨planeMap, h_planeMap_lip, h_planeMap_unit, h_planeMap_incidence, h_local_ad⟩

  -- Global AD (Case 1: outputLoss > sigma): constant slope 0
  have globalGrains : PureWZ2LipschitzGlobalGrainData binShading sigma
      (Kakeya.realRpowENN delta (-outputLoss)) := by
    let slope : ℝ → ℝ := fun _ => 0
    have hslope_lip : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1) := by
      intro x _ y _
      simp [slope, dist_eq_norm] <;> norm_num
    have hglobal_ad : ∀ (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 →
        PureWZ2PaperADSet1
          (scalarProjection (globalGrainDirection (slope z))
            (horizontalSlice binShading.union z))
          delta (1 - sigma) (Kakeya.realRpowENN delta (-outputLoss)) := by
      intro z hz
      have h_dir : globalGrainDirection (slope z) = globalGrainDirection (0 : ℝ) := by
        simp [slope]
      rw [h_dir]
      have h_slice_sub : horizontalSlice binShading.union z ⊆ horizontalSlice shading.union z := by
        intro x hx
        exact ⟨h_sub_union hx.1, hx.2⟩
      have h_img_sub : scalarProjection (globalGrainDirection (0 : ℝ))
          (horizontalSlice binShading.union z) ⊆
        scalarProjection (globalGrainDirection (0 : ℝ)) (horizontalSlice shading.union z) :=
        image_mono h_slice_sub
      have h_proj_bounded : scalarProjection (globalGrainDirection (0 : ℝ))
          (horizontalSlice binShading.union z) ⊆ Set.Icc (-(1 : ℝ)) (1 : ℝ) :=
        h_img_sub.trans (horizontal_slice_projection_bounded z)
      have h_interval_eq : Set.Icc (-(2 : ℝ) / 2) (2 / 2) = Set.Icc (-(1 : ℝ)) (1 : ℝ) := by norm_num
      have h_proj_bounded' : scalarProjection (globalGrainDirection (0 : ℝ))
          (horizontalSlice binShading.union z) ⊆ Set.Icc (-(2 : ℝ) / 2) (2 / 2) := by
        rw [h_interval_eq]
        exact h_proj_bounded
      have h_loss_gt_sigma : sigma < outputLoss := by linarith
      exact bounded_interval_paper_ad1
        hdelta_pos hdelta_lt_one.le hsigma_pos hsigma_lt_one
        h_loss_gt_sigma (by norm_num) hsmall_global h_proj_bounded'
    exact PureWZ2LipschitzGlobalGrainData.ofRealFunction
      slope hslope_lip hglobal_ad

  exact ⟨family, binShading, line_class, h_bin_cubical, extremal_output, cwa_output,
    globalGrains, localGrains⟩

end Kakeya.Assouad

end
