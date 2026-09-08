import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebra helpers for the generalized Frostman estimate

This module collects reusable ENNReal and real-power lemmas, plus the
Frostman-constant lower bound and multiplicity transfer inequality used in
the final algebra node.

## Main results

- `frostmanConstant_ge_one`: `C_F ≥ 1` for a nonempty unit-ball family.
- `realRpowENN_rpow`: `(δ^a)^b = δ^(a*b)` in `ENNReal`.
- `multiplicity_transfer`: transfer a multiplicity bound back from a
  translated subfamily to the original shading.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ### Frostman constant lower bound -/

/-- For a nonempty tube family in the unit ball, the Frostman constant
relative to the unit ball is at least `1`. -/
lemma frostmanConstant_ge_one {δ : ℝ} (hδ_pos : 0 < δ) {F : TubeFamily δ}
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall) :
    1 ≤ F.toBodyFamily.frostmanConstantIn unitBall.carrier := by
  classical
  let BF := F.toBodyFamily
  let U := unitBall.carrier
  have hU_conv : Convex ℝ U := convex_closedBall (0 : Point3) 1
  have hU_vol_pos : 0 < volume U :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hU_vol_ne_top : volume U ≠ ⊤ :=
    IsCompact.measure_lt_top (isCompact_closedBall (0 : Point3) 1) |>.ne
  have h_all_contained : BF.containedMass U = BF.mass := by
    have h_indices : BF.containedIndices U = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      have h : (BF.body i).carrier ⊆ U := by
        have h' : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
        have h_eq1 : (BF.body i).carrier = (F.tube i).carrier := by rfl
        have h_eq2 : U = Kakeya.DeltaTube.unitBall := by rfl
        rw [h_eq1, h_eq2]
        exact h'
      exact h
    rw [BodyFamily.containedMass, h_indices]; rfl
  have h_vol_pos : ∀ (i : Fin F.card), 0 < (F.tube i).volume := by
    intro i
    have h_eq : (F.tube i).volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume (F.tube i)
    rw [h_eq]
    exact RandomTranslation.deltaTubeVolume_pos hδ_pos
  let i0 : Fin F.card := ⟨0, hF_nonempty⟩
  have h_mass_pos : 0 < BF.mass := by
    dsimp only [BodyFamily.mass]
    let f : Fin F.card → ENNReal := fun i => (BF.body i).volume
    have h_le : f i0 ≤ ∑ i : Fin F.card, f i :=
      Finset.single_le_sum (fun i _ => show 0 ≤ f i from by simp) (Finset.mem_univ i0)
    have h_pos : 0 < f i0 := h_vol_pos i0
    exact lt_of_lt_of_le h_pos h_le
  have h_vol_ne_top : ∀ (i : Fin F.card), (F.tube i).volume ≠ ⊤ := by
    intro i
    have h_eq : (F.tube i).volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume (F.tube i)
    rw [h_eq]
    exact RandomTranslation.deltaTubeVolume_ne_top
  have h_mass_ne_top : BF.mass ≠ ⊤ := by
    dsimp only [BodyFamily.mass]
    rw [ENNReal.sum_ne_top]
    intro i _
    have h_eq : (BF.body i).volume = (F.tube i).volume := by rfl
    rw [h_eq]
    exact h_vol_ne_top i
  have h_density_pos : 0 < BF.density U := by
    rw [BodyFamily.density, h_all_contained]
    exact ENNReal.div_pos h_mass_pos.ne' hU_vol_ne_top
  have h_density_ne_top : BF.density U ≠ ⊤ := by
    rw [BodyFamily.density, h_all_contained]
    exact ENNReal.div_ne_top h_mass_ne_top hU_vol_pos.ne'
  have h_self_ratio : BF.density U / BF.density U = 1 :=
    ENNReal.div_self h_density_pos.ne' h_density_ne_top
  have h1_in_set : (1 : ENNReal) ∈
      {c : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ K ⊆ U ∧
        c = BF.density K / BF.density U} := by
    refine ⟨U, hU_conv, Set.Subset.refl U, ?_⟩
    rw [h_self_ratio]
  have h_bdd : BddAbove {c : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ K ⊆ U ∧
      c = BF.density K / BF.density U} := by
    use ⊤
    intro x _
    exact le_top
  exact le_csSup h_bdd h1_in_set

/-- For a nonempty tube family in the unit ball, the Frostman constant
satisfies `C_F * F.mass ≥ volume unitBall`. -/
lemma frostmanConstant_mul_mass_ge_volume {δ : ℝ} (hδ_pos : 0 < δ) {F : TubeFamily δ}
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall) :
    F.toBodyFamily.frostmanConstantIn unitBall.carrier * F.toBodyFamily.mass ≥
      volume unitBall.carrier := by
  classical
  let BF := F.toBodyFamily
  let U := unitBall.carrier
  have hU_conv : Convex ℝ U := convex_closedBall (0 : Point3) 1
  have hU_vol_pos : 0 < volume U :=
    Metric.measure_closedBall_pos volume (0 : Point3) (by norm_num)
  have hU_vol_ne_top : volume U ≠ ⊤ :=
    IsCompact.measure_lt_top (isCompact_closedBall (0 : Point3) 1) |>.ne
  have h_all_contained : BF.containedMass U = BF.mass := by
    have h_indices : BF.containedIndices U = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      have h : (BF.body i).carrier ⊆ U := by
        have h' : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
        have h_eq1 : (BF.body i).carrier = (F.tube i).carrier := by rfl
        have h_eq2 : U = Kakeya.DeltaTube.unitBall := by rfl
        rw [h_eq1, h_eq2]; exact h'
      exact h
    rw [BodyFamily.containedMass, h_indices]; rfl
  have h_vol_pos : ∀ (i : Fin F.card), 0 < (F.tube i).volume := by
    intro i
    have h_eq : (F.tube i).volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume (F.tube i)
    rw [h_eq]; exact RandomTranslation.deltaTubeVolume_pos hδ_pos
  have h_vol_ne_top : ∀ (i : Fin F.card), (F.tube i).volume ≠ ⊤ := by
    intro i
    have h_eq : (F.tube i).volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume (F.tube i)
    rw [h_eq]; exact RandomTranslation.deltaTubeVolume_ne_top
  have h_mass_pos : 0 < BF.mass := by
    dsimp only [BodyFamily.mass]
    let i0 : Fin F.card := ⟨0, hF_nonempty⟩
    let f : Fin F.card → ENNReal := fun i => (BF.body i).volume
    have h_le : f i0 ≤ ∑ i : Fin F.card, f i :=
      Finset.single_le_sum (fun i _ => show 0 ≤ f i from by simp) (Finset.mem_univ i0)
    have h_pos : 0 < f i0 := h_vol_pos i0
    exact lt_of_lt_of_le h_pos h_le
  have h_mass_ne_top : BF.mass ≠ ⊤ := by
    dsimp only [BodyFamily.mass]
    rw [ENNReal.sum_ne_top]
    intro i _
    have h_eq : (BF.body i).volume = (F.tube i).volume := by rfl
    rw [h_eq]; exact h_vol_ne_top i
  let i0 : Fin F.card := ⟨0, hF_nonempty⟩
  let K : Set Point3 := (F.tube i0).carrier
  have hK_conv : Convex ℝ K := GeometricLemmas.deltaTube_carrier_convex (F.tube i0)
  have hK_sub : K ⊆ U := hF_ball i0
  have hK_vol_pos : 0 < volume K := h_vol_pos i0
  have hK_vol_ne_top : volume K ≠ ⊤ := h_vol_ne_top i0
  have h_contained_K : volume K ≤ BF.containedMass K := by
    have h_i0_in : i0 ∈ BF.containedIndices K := by
      have h_sub : (BF.body i0).carrier ⊆ K := by
        have h_eq : (BF.body i0).carrier = K := by
          simp [K, BF, BodyFamily.body] <;> rfl
        rw [h_eq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i0, h_sub⟩
    have h : BF.containedMass K = ∑ i ∈ BF.containedIndices K, (BF.body i).volume := by rfl
    rw [h]
    have h2 : (BF.body i0).volume ≤ ∑ i ∈ BF.containedIndices K, (BF.body i).volume :=
      Finset.single_le_sum (fun i _ => show 0 ≤ (BF.body i).volume from by positivity) h_i0_in
    exact h2
  have h_density_K_ge_one : 1 ≤ BF.density K := by
    dsimp only [BodyFamily.density]
    have h : (volume K : ENNReal) ≤ BF.containedMass K := h_contained_K
    have h' : (1 : ENNReal) ≤ BF.containedMass K / volume K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hK_vol_pos.ne') (Or.inl hK_vol_ne_top)]
      <;> simpa using h
    exact h'
  have h_densityU_pos : 0 < BF.density U := by
    rw [BodyFamily.density, h_all_contained]
    exact ENNReal.div_pos h_mass_pos.ne' hU_vol_ne_top
  have h_densityU_ne_top : BF.density U ≠ ⊤ := by
    rw [BodyFamily.density, h_all_contained]
    exact ENNReal.div_ne_top h_mass_ne_top hU_vol_pos.ne'
  have h2 : 1 / BF.density U = volume U / BF.mass := by
    dsimp only [BodyFamily.density]
    rw [h_all_contained]
    have h3 : 1 / (BF.mass / volume U) = volume U / BF.mass := by
      have h4 : (1 : ENNReal) / (BF.mass / volume U) = (BF.mass / volume U)⁻¹ := by
        simp
      rw [h4]
      exact ENNReal.inv_div (Or.inl hU_vol_ne_top) (Or.inl hU_vol_pos.ne')
    exact h3
  have h_ratio_ge : BF.density K / BF.density U ≥ volume U / BF.mass := by
    have h1 : BF.density K / BF.density U ≥ 1 / BF.density U := by
      gcongr
    rw [h2] at h1
    exact h1
  have hK_in_set : (BF.density K / BF.density U) ∈
      {c : ENNReal | ∃ (K' : Set Point3), Convex ℝ K' ∧ K' ⊆ U ∧
        c = BF.density K' / BF.density U} := by
    exact ⟨K, hK_conv, hK_sub, rfl⟩
  have h_bdd : BddAbove {c : ENNReal | ∃ (K' : Set Point3), Convex ℝ K' ∧ K' ⊆ U ∧
      c = BF.density K' / BF.density U} := by
    use ⊤; intro x _; exact le_top
  have h_CF_ge_K : BF.density K / BF.density U ≤ BF.frostmanConstantIn U :=
    le_csSup h_bdd hK_in_set
  have h_CF_ge : volume U / BF.mass ≤ BF.frostmanConstantIn U :=
    le_trans h_ratio_ge h_CF_ge_K
  have h_final : BF.frostmanConstantIn U * BF.mass ≥ volume U := by
    calc
      BF.frostmanConstantIn U * BF.mass
        ≥ (volume U / BF.mass) * BF.mass := by gcongr
      _ = volume U := by
        rw [ENNReal.div_mul_cancel h_mass_pos.ne' h_mass_ne_top]
  exact h_final

/-! ### realRpowENN algebra -/

/-- Power of a power: `(realRpowENN δ a)^b = realRpowENN δ (a*b)`. -/
lemma realRpowENN_rpow {δ a b : ℝ} (hδ_pos : 0 < δ) :
    (Kakeya.realRpowENN δ a)^b = Kakeya.realRpowENN δ (a * b) := by
  have h1 : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ_pos a
  have h2 : (Kakeya.realRpowENN δ a)^b =
      ENNReal.ofReal ((Real.rpow δ a)^b) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_rpow_of_pos h1
  rw [h2]
  have h3 : (Real.rpow δ a)^b = Real.rpow δ (a * b) := by
    have h4 : Real.rpow δ (a * b) = (Real.rpow δ a)^b :=
      Real.rpow_mul (by linarith) a b
    exact h4.symm
  rw [h3]; rfl

/-- Multiplication-addition identity for `realRpowENN`. -/
lemma realRpowENN_add {δ a b : ℝ} (hδ_pos : 0 < δ) :
    Kakeya.realRpowENN δ (a + b) =
      Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow δ (a + b) = Real.rpow δ a * Real.rpow δ b :=
    Real.rpow_add (by linarith) a b
  rw [h1]
  have ha : 0 ≤ Real.rpow δ a := Real.rpow_nonneg (by linarith) a
  have hb : 0 ≤ Real.rpow δ b := Real.rpow_nonneg (by linarith) b
  have h_mul : ENNReal.ofReal (Real.rpow δ a * Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) := by
    rw [← ENNReal.ofReal_mul ha]
  exact h_mul

/-- Product identity for `realRpowENN`: `(a*b)^c = a^c * b^c` for positive `a, b`. -/
lemma realRpowENN_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    Kakeya.realRpowENN (a * b) c =
      Kakeya.realRpowENN a c * Kakeya.realRpowENN b c := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow (a * b) c = Real.rpow a c * Real.rpow b c :=
    Real.mul_rpow (by linarith) (by linarith)
  rw [h1]
  have ha' : 0 ≤ Real.rpow a c := Real.rpow_nonneg (by linarith) c
  rw [← ENNReal.ofReal_mul ha']

/-! ### Multiplicity transfer -/

/-- Transfer an average-multiplicity bound from a translated subfamily
shading `Y'` back to the original shading `Y`.

If `Y'.mass ≥ c * Y.mass`, `volume Y'.union ≤ J * volume Y.union`, and
`Y'.mass ≤ M' * volume Y'.union`, then
`Y.mass ≤ (J / c) * M' * volume Y.union`. -/
lemma multiplicity_transfer {F G : BodyFamily}
    {Y : Shading F} {Y' : Shading G}
    {c J M' : ENNReal}
    (hc_pos : 0 < c) (hc_ne_top : c ≠ ⊤)
    (h_mass : c * Y.mass ≤ Y'.mass)
    (h_union : volume Y'.union ≤ J * volume Y.union)
    (h_mult : Y'.mass ≤ M' * volume Y'.union) :
    Y.mass ≤ (J / c) * M' * volume Y.union := by
  have h1 : c * Y.mass ≤ M' * volume Y'.union :=
    le_trans h_mass h_mult
  have h2 : c * Y.mass ≤ M' * (J * volume Y.union) :=
    calc c * Y.mass
      ≤ M' * volume Y'.union := h1
    _ ≤ M' * (J * volume Y.union) := by gcongr
  have h3 : c * Y.mass ≤ (J * M') * volume Y.union := by
    have h4 : M' * (J * volume Y.union) = (J * M') * volume Y.union := by ring
    rw [h4] at h2
    exact h2
  have hc_ne_zero : c ≠ 0 := hc_pos.ne'
  have h5 : Y.mass ≤ c⁻¹ * ((J * M') * volume Y.union) := by
    have h6 : c⁻¹ * (c * Y.mass) ≤ c⁻¹ * ((J * M') * volume Y.union) := by
      gcongr
    have h7 : c⁻¹ * (c * Y.mass) = Y.mass := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc_ne_zero hc_ne_top]; ring
    rw [h7] at h6
    exact h6
  have h8 : c⁻¹ * ((J * M') * volume Y.union) =
      (J / c) * M' * volume Y.union := by
    simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [h8] at h5
  exact h5

/-! ### Frostman normalization wrapper -/

/-- Wrap `frostman_from_deltaMax` for tube families.

Given `deltaMax ≤ C` and `containedMass U ≥ m`, conclude
`IsCFrostmanIn U (C * volume U / m)`.

This is a direct application of `BodyFamily.frostman_from_deltaMax`. -/
lemma frostman_normalize_from_deltaMax {δ : ℝ} {F : TubeFamily δ}
    (U : Set Point3) (C m : ENNReal)
    (hm_pos : 0 < m) (hm_ne_top : m ≠ ⊤)
    (hU_vol_pos : 0 < volume U) (hU_vol_ne_top : volume U ≠ ⊤)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (h_containedMass : F.toBodyFamily.containedMass U ≥ m) :
    F.toBodyFamily.IsCFrostmanIn U (C * volume U / m) :=
  BodyFamily.frostman_from_deltaMax hm_pos hm_ne_top hU_vol_pos hU_vol_ne_top
    h_deltaMax h_containedMass

/-! ### Density loss absorption -/

/-- Absorb a constant density loss by slightly weakening the exponent.

If `Y` is `δ^η`-dense over `F`, `YS` retains at least `Y.mass / C` of the
shaded mass, and `S.mass ≤ F.mass`, then for `δ` small enough that
`C ≤ δ^(-ε/4)`, the selected shading `YS` is `δ^(η+ε/4)`-dense over `S`.

The constant factor `C` is absorbed into the slack `ε/4` in the exponent. -/
lemma isLambdaDense_absorb_constant
    {δ : ℝ} (hδ_pos : 0 < δ)
    {F S : BodyFamily} {Y : Shading F} {YS : Shading S}
    {C : ENNReal} (hC_pos : 0 < C) (hC_ne_top : C ≠ ⊤)
    {η ε : ℝ} (hε_pos : 0 < ε)
    (h_small : C ≤ Kakeya.realRpowENN δ (-ε / 4))
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ η))
    (hS_mass_le : S.mass ≤ F.mass)
    (h_mass_retention : Y.mass / C ≤ YS.mass) :
    YS.IsLambdaDense (Kakeya.realRpowENN δ (η + ε / 4)) := by
  have h_add : Kakeya.realRpowENN δ (η + ε / 4) =
      Kakeya.realRpowENN δ η * Kakeya.realRpowENN δ (ε / 4) :=
    realRpowENN_add hδ_pos
  have h_eps_pos : 0 < Real.rpow δ (ε / 4) := Real.rpow_pos_of_pos hδ_pos (ε / 4)
  have h_neg_inv : Kakeya.realRpowENN δ (-ε / 4) =
      (Kakeya.realRpowENN δ (ε / 4))⁻¹ := by
    simp only [Kakeya.realRpowENN]
    have h1 : Real.rpow δ (-ε / 4) = (Real.rpow δ (ε / 4))⁻¹ := by
      have h2 : -ε / 4 = -(ε / 4) := by ring
      rw [h2]
      exact Real.rpow_neg (le_of_lt hδ_pos) (ε / 4)
    rw [h1]
    rw [ENNReal.ofReal_inv_of_pos h_eps_pos]
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have h_eps_le : Kakeya.realRpowENN δ (ε / 4) ≤ C⁻¹ := by
    rw [h_neg_inv] at h_small
    exact ENNReal.le_inv_iff_le_inv.mp h_small
  have h_main : Kakeya.realRpowENN δ (η + ε / 4) * S.mass ≤ YS.mass := by
    calc
      Kakeya.realRpowENN δ (η + ε / 4) * S.mass
        = (Kakeya.realRpowENN δ η * Kakeya.realRpowENN δ (ε / 4)) * S.mass := by
          rw [h_add]
      _ ≤ (Kakeya.realRpowENN δ η * C⁻¹) * S.mass := by gcongr
      _ = (Kakeya.realRpowENN δ η * S.mass) * C⁻¹ := by ring
      _ ≤ (Kakeya.realRpowENN δ η * F.mass) * C⁻¹ := by gcongr
      _ = (Kakeya.realRpowENN δ η * F.mass) / C := by
        simp [div_eq_mul_inv]
      _ ≤ Y.mass / C := by
        have h_dense : Kakeya.realRpowENN δ η * F.mass ≤ Y.mass := hY_dense
        gcongr
      _ ≤ YS.mass := h_mass_retention
  exact h_main

/-- Absorb a finite constant into a negative power of δ.

For any `K ≠ ⊤` and `ε > 0`, there exists `δ₀ > 0` such that
`K ≤ δ^(-ε)` for all `0 < δ ≤ δ₀`. -/
lemma absorb_const {K : ENNReal} (hK_ne_top : K ≠ ⊤)
    {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
        K ≤ Kakeya.realRpowENN δ (-ε) := by
  by_cases hK0 : K = 0
  · refine ⟨1, by norm_num, by norm_num, fun δ _ _ => ?_⟩
    rw [hK0] <;> positivity
  · have hK_pos : 0 < K := Ne.bot_lt hK0
    have hK_lt_top : K < ⊤ := lt_top_iff_ne_top.mpr hK_ne_top
    have hK_real_pos : 0 < K.toReal :=
      ENNReal.toReal_pos_iff.mpr ⟨hK_pos, hK_lt_top⟩
    let a : ℝ := K.toReal ^ (-ε⁻¹)
    have ha_pos : 0 < a := Real.rpow_pos_of_pos hK_real_pos _
    let delta₀ : ℝ := min 1 a
    have hδ₀_pos : 0 < delta₀ := by positivity
    have hδ₀_le_one : delta₀ ≤ 1 := min_le_left _ _
    refine ⟨delta₀, hδ₀_pos, hδ₀_le_one, ?_⟩
    intro δ hδ_pos hδ_le
    have h2 : δ ≤ a := le_trans hδ_le (min_le_right _ _)
    have h_neg : -ε < 0 := by linarith
    have h3 : a ^ (-ε) ≤ δ ^ (-ε) := by
      by_cases hlt : δ < a
      · exact (Real.strictAntiOn_rpow_Ioi_of_exponent_neg h_neg hδ_pos ha_pos hlt).le
      · have heq : δ = a := by linarith
        rw [heq]
    have h4 : a ^ (-ε) = K.toReal := by
      dsimp only [a]
      rw [← Real.rpow_mul (by linarith)]
      have h5 : (-ε⁻¹) * (-ε) = 1 := by
        field_simp [hε_pos.ne'] <;> ring
      rw [h5] <;> simp
    have h6 : K.toReal ≤ δ ^ (-ε) := by
      rw [h4] at h3 <;> exact h3
    have h7 : K = ENNReal.ofReal K.toReal := by
      rw [ENNReal.ofReal_toReal hK_ne_top]
    rw [h7]
    have h8 : Kakeya.realRpowENN δ (-ε) = ENNReal.ofReal (δ ^ (-ε)) := by
      simp [Kakeya.realRpowENN]
    rw [h8]
    exact ENNReal.ofReal_le_ofReal h6

end Kakeya.Streamlined.GeneralizedFrostman
