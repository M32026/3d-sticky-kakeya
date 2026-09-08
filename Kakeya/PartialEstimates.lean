/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Shading
public import Kakeya.KatzTao
public import Kakeya.Frostman
public import Kakeya.Density
public import Kakeya.Discretization
public import Kakeya.Tube.EDUpToMult
public import Kakeya.Multiplicity
public import Kakeya.Probability
public import Kakeya.RandomTranslation.RandCF
public import Kakeya.RandomTranslation.RigidRandCFFinal
public import Kakeya.Asymptotics
public import Kakeya.Mathlib.ENNReal
public import Kakeya.FrostmanConstant

/-!
We formalise [GWZ, Definition 3.4] and [GWZ, Definition 3.5]
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

section KatzTaoEstimate

universe u

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The partial Kakeya estimate at exponent `β`. -/
def KatzTaoEstimate (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∑ i ∈ s, volume (T i).shade ≤ δ ^ (- ε) * s.card ^ β * volume (⋃ i ∈ s, (T i).shade)

/-- Base case: the partial Kakeya estimate holds at `β = 1` in any Euclidean space. -/
theorem KatzTao_one {n : ℕ} : KatzTaoEstimate (EuclideanSpace ℝ (Fin n)) 1 := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hB hKT hf
  have h_sum_le : (∑ i ∈ s, volume (T i).shade) ≤
      s.card * volume (⋃ i ∈ s, (T i).shade) := by
    calc ∑ i ∈ s, volume (T i).shade
        ≤ ∑ _ ∈ s, volume (⋃ j ∈ s, (T j).shade) :=
          Finset.sum_le_sum fun i hi =>
            measure_mono fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
      _ = s.card * volume (⋃ j ∈ s, (T j).shade) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_one_le : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε) := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one (by exact_mod_cast hδ1.le) hε.le
  calc ∑ i ∈ s, volume (T i).shade
      ≤ s.card * volume (⋃ i ∈ s, (T i).shade) := h_sum_le
    _ = 1 * ((s.card : ENNReal) ^ (1 : ℝ)) * volume (⋃ i ∈ s, (T i).shade) := by
        rw [ENNReal.rpow_one, one_mul]
    _ ≤ (δ : ENNReal) ^ (-ε) * ((s.card : ENNReal) ^ (1 : ℝ)) *
          volume (⋃ i ∈ s, (T i).shade) := by gcongr

section
variable {E}

/-- The partial Katz-Tao estimate is monotone in `β`: a smaller exponent gives a stronger
bound, so `K_KT(β)` for `β ≤ β'` implies `K_KT(β')`. -/
theorem KatzTaoEstimate.mono {β β' : ℝ} (hββ' : β ≤ β')
    (h : KatzTaoEstimate.{u} E β) : KatzTaoEstimate.{u} E β' := by
  intro ε hε
  obtain ⟨η, hη, hh⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hh] with δ hh_δ
  intro ι s T hball hKT hfull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs; simp
  refine (hh_δ s T hball hKT hfull).trans ?_
  have hone : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  gcongr

end

/-- Upgrade `KatzTaoEstimate E β` to the corresponding multiplicity bound, with the Katz-Tao
parameter `τ` allowed to range below `δ`. -/
theorem KatzTaoEstimate.generalize [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((τ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ β := by
  intro ε hε
  obtain ⟨η₁, hη₁, hh⟩ := h ε hε
  set n : ℕ := Module.finrank ℝ E with hn_def
  set M : ℝ := (n : ℝ) + η₁ + 1 with hM_def
  have hM_pos : 0 < M := by positivity
  have hn : 0 < n := by (expose_names; exact (Module.finrank_pos_iff_of_free ℝ E).mpr inst_5)
  set η : ℝ := ε * η₁ / M with hη_def
  set C : NNReal := Tube.card_le_of_densityIn_le.C n with hC_def
  set δ₀ : NNReal := ⟨(1 / ((C : ℝ) + 1)) ^ (M / (2 * ε)),
    Real.rpow_nonneg (by positivity) _⟩ with hδ₀_def
  refine ⟨η, by positivity, ?_⟩
  filter_upwards [hh, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one),
    Ioo_mem_nhdsGT (show (0 : NNReal) < δ₀ from NNReal.coe_lt_coe.mp
      (Real.rpow_pos_of_pos (by positivity) _))]
    with δ hh_δ ⟨hδ0, hδ1⟩ ⟨_, hδ_lt_δ₀⟩
  intro τ hτ_pos hτ_le_δ ι s T hball hKT hfull
  by_cases hcase : (δ : ENNReal) ^ (M / ε) ≤ (τ : ENNReal)
  · have h_key : (δ : ENNReal) ^ η₁ ≤ (τ : ENNReal) ^ η := by
      rw [show η₁ = M / ε * η by change η₁ = M / ε * (ε * η₁ / M); field_simp,
          ENNReal.rpow_mul]
      exact ENNReal.rpow_le_rpow hcase (by positivity)
    have h_δτε : (δ : ENNReal) ^ (-ε) ≤ (τ : ENNReal) ^ (-ε) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr
        (ENNReal.rpow_le_rpow (by exact_mod_cast hτ_le_δ) hε.le)
    rw [multiplicity_le_iff]
    refine (hh_δ s T hball
      (hKT.mono <| by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]; exact ENNReal.inv_le_inv.mpr h_key)
      ((show (δ : NNReal) ^ η₁ ≤ (τ : NNReal) ^ η by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg _ hη₁.le,
            ENNReal.coe_rpow_of_nonneg _ (by positivity : (0:ℝ) ≤ η)]
        exact h_key).trans hfull)).trans (by gcongr)
  · push Not at hcase
    by_cases hcard_zero : s.card = 0
    · simp [Finset.card_eq_zero.mp hcard_zero]
    calc multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (s.card : ENNReal) := multiplicity_le_card s _
      _ ≤ (C : ENNReal) * (τ : ENNReal) ^ (-η) * (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
          convert Tube.card_le_of_densityIn_le (δ := δ) (T := fun i ↦ (T i).toTube)
            (by exact_mod_cast hδ0.ne') hball
            ((le_maxDensity s _ _).trans hKT) using 2
          rw [show (-((n : ℝ) - 1) : ℝ) = ((-(((n : ℕ) : ℤ) - 1) : ℤ) : ℝ) from by
            push_cast; ring, ENNReal.rpow_intCast]
      _ ≤ (τ : ENNReal) ^ (-(2 * ε / M)) * (τ : ENNReal) ^ (-η) *
            (τ : ENNReal) ^ (-(((n : ℝ) - 1) * (ε / M))) := by
          have h_τ_ε_le_δ : (τ : ENNReal) ^ (ε / M) ≤ (δ : ENNReal) := by
            calc (τ : ENNReal) ^ (ε / M)
                ≤ ((δ : ENNReal) ^ (M / ε)) ^ (ε / M) :=
                  ENNReal.rpow_le_rpow hcase.le (by positivity)
              _ = (δ : ENNReal) := by
                  rw [← ENNReal.rpow_mul,
                      show M / ε * (ε / M) = 1 from by field_simp, ENNReal.rpow_one]
          have h_δτ : (δ : ENNReal) ^ (-((n : ℝ) - 1)) ≤
              (τ : ENNReal) ^ (-(((n : ℝ) - 1) * (ε / M))) := by
            rw [ENNReal.rpow_neg, ENNReal.rpow_neg, mul_comm, ENNReal.rpow_mul]
            exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow h_τ_ε_le_δ
              (by linarith [show (1:ℝ) ≤ n from by exact_mod_cast hn]))
          have hC_le : (C : ENNReal) ≤ (τ : ENNReal) ^ (-(2 * ε / M)) := by
            rw [ENNReal.rpow_neg]
            refine ENNReal.le_inv_iff_mul_le.mpr <| calc
              (C : ENNReal) * (τ : ENNReal) ^ (2 * ε / M)
                  ≤ ((C : ENNReal) + 1) * (δ : ENNReal) ^ (2 * ε / M) := by
                    gcongr; exact le_self_add
                _ = ((((C : NNReal) + 1) * δ ^ (2 * ε / M) : NNReal) : ENNReal) := by
                    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
                    push_cast; rfl
                _ ≤ 1 := by
                    exact_mod_cast show ((C : ℝ) + 1) * (δ : ℝ) ^ (2 * ε / M) ≤ 1 by
                      rw [mul_comm]
                      refine (le_div_iff₀ (by positivity)).mp ?_
                      have := Real.rpow_le_rpow (by exact_mod_cast hδ0.le) hδ_lt_δ₀.le
                        (by positivity : (0:ℝ) ≤ 2 * ε / M)
                      rwa [← Real.rpow_mul (by positivity),
                           show M / (2 * ε) * (2 * ε / M) = 1 from by field_simp,
                           Real.rpow_one] at this
          gcongr
      _ = (τ : ENNReal) ^ (-ε) := by
          rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hτ_pos.ne') ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ (by exact_mod_cast hτ_pos.ne') ENNReal.coe_ne_top]
          congr 1
          rw [hη_def, hM_def]; field_simp; ring
      _ ≤ (τ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ β := by
          refine le_mul_of_one_le_right' ?_
          rcases hβ_0.lt_or_eq with hβ_pos | hβ_eq
          · exact ENNReal.one_le_rpow
              (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard_zero) hβ_pos
          · rw [← hβ_eq, ENNReal.rpow_zero]


/-- For any divisor `c > 0` and exponent `η > 0`, eventually
`exp(-δ^(-η)/c) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_le_div_five {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), Real.exp (-δ ^ (-η) / c) ≤ 1/5 := by
  filter_upwards [absorb_const_le_rpow_neg
    (mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 5))) hη] with δ hδ
  rw [show (-δ ^ (-η) / c : ℝ) = -(δ ^ (-η) / c) from by ring]
  refine (Real.exp_le_exp.mpr (show -(δ ^ (-η) / c) ≤ -Real.log 5 by
    rw [neg_le_neg_iff, le_div_iff₀ hc]; linarith)).trans ?_
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

/-- Eventually `2^β ≤ δ^(-ε)` as `δ → 0⁺`, for any `β : ℝ` and `ε > 0`. -/
private lemma absorb_two_rpow_le_rpow_neg (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (2 : ℝ) ^ β ≤ δ ^ (-ε) :=
  absorb_const_le_rpow_neg (Real.rpow_pos_of_pos two_pos β) hε

/-- Eventually `4 * K^4 ≤ δ^(-η)` as `δ → 0⁺`, for `K, η > 0`. -/
private lemma absorb_four_K4_le_rpow_neg {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), 4 * K ^ 4 ≤ δ ^ (-η) :=
  absorb_const_le_rpow_neg (by positivity) hη

/-- Eventually `exp(-δ^(η/2 - 2η/2) / (8K^2)) ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_exp_K_le_div_five {K η : ℝ} (_hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      Real.exp (-δ ^ (η / 2 - 2 * η / 2) / (8 * K ^ 2)) ≤ 1/5 := by
  filter_upwards [absorb_exp_le_div_five (by positivity : (0 : ℝ) < 8 * K^2)
    (half_pos hη)] with δ hδ
  rwa [show (η / 2 - 2 * η / 2 : ℝ) = -(η / 2) from by ring]

/-- Eventually `δ ≤ 1/5` as `δ → 0⁺`. -/
private lemma absorb_delta_le_div_five :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), δ ≤ 1/5 := by
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/5))
  intro δ hδ
  simp only [Set.mem_Ioo] at hδ
  linarith [hδ.2]

/-- The lower volume bound for a `δ`-tube, in `ℝ`-valued (`volume.real`) form.
TODO: remove use of volume.real
-/
private lemma tube_le_volume_real [Nontrivial E] {δ : NNReal} (T : ShadedTube δ E) :
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤
      volume.real T.carrier := by
  have hreal := ENNReal.toReal_mono T.isCompact'.measure_lt_top.ne (Tube.le_volume T.toTube)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.coe_toReal] using hreal

/-- [GWZ, Lemma 3.7] `KKT(β)` implies a multiplicity bound for sets of `δ`-tubes
with any value of `Δ_max(T)`. -/
theorem KatzTaoEstimate.multiplicity_bound [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  intro ε hε
  obtain ⟨η1, hη1_pos, hKKT⟩ := h (ε / 4) (by linarith)
  set η_K := min (η1 / 2) (ε / 8) with hη_K_def
  have hη_K_pos : 0 < η_K := lt_min (half_pos hη1_pos) (by linarith)
  refine ⟨η_K / 2, half_pos hη_K_pos, ?_⟩
  set c_low : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hc_up_def
  set K_unif : ℝ := c_up / c_low with hK_unif_def
  have hK_unif_pos : 0 < K_unif := div_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos _)) hc_low_pos
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Density test family constants: the discretization constants of
  -- `exists_localized_finite_test_family_maxDensity` at radius `R = 1`. The exponent is padded by
  -- `+1` so that the multiplicative constant `Ctest` can be absorbed into `δ ^ (-Mtest)` for
  -- small `δ` (the `hδ_lt_invCtest` conjunct below).
  set Ctest : ℝ := (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
    with hCtest_def
  set Mtest : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) + 1
    with hMtest_def
  have hCtest_pos : 0 < Ctest :=
    NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
  have hMtest_pos : 0 < Mtest := by
    rw [hMtest_def]
    linarith [exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)]
  filter_upwards [hKKT,
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_two_rpow_le_rpow_neg β (ε := ε / 4) (by linarith)),
      nnreal_eventually_of_real_eventually
        (absorb_four_K4_le_rpow_neg (K := K_unif) (η := η_K / 2) hK_unif_pos (half_pos hη_K_pos)),
      nnreal_eventually_of_real_eventually
        (absorb_log_le_rpow_neg (C := Ctest) (M := 8 * Mtest + 8) (η := η_K)
          hCtest_pos (by linarith) hη_K_pos),
      nnreal_eventually_of_real_eventually
        (absorb_exp_K_le_div_five (K := K_unif) (η := η_K) hK_unif_pos hη_K_pos),
      nnreal_eventually_of_real_eventually absorb_delta_le_div_five,
      nnreal_eventually_of_real_eventually (p := fun δ => δ < 1 / Ctest)
        (nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hCtest_pos)))]
    with δNN hδ_KKT hδ_lt_one hδ_pos h_2β_le hδ_small_K hδ_small_b
         hδ5_c hδ5_b hδ_lt_invCtest
  set δ : ℝ := (δNN : ℝ) with hδ_def
  have hδNN_pos : (0 : NNReal) < δNN := by exact_mod_cast hδ_pos
  intro ι s T hB hfull
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  set Δ : ℝ := (maxDensity s W).toReal with hΔ_def
  have hT_vol_lb_real : ∀ i,
      c_low * δ ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier :=
    fun i => tube_le_volume_real E (T i)
  rcases eq_or_ne s ∅ with rfl | hs
  · simp only [ShadedBody.multiplicity_empty]
    exact bot_le
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hvol_pos : 0 < volume (W i₀).carrier :=
      (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le
        (mul_pos hc_low_pos (pow_pos hδ_pos _)) (hT_vol_lb_real i₀))).1
    have hΔ_pos : 0 < Δ :=
      ENNReal.toReal_pos
        (zero_lt_one.trans_le (one_le_maxDensity ⟨i₀, hi₀, hvol_pos⟩)).ne'
        (maxDensity_ne_top s W)
    have hT_unif : ∀ i ∈ s, ∀ j ∈ s,
        volume.real (T i).carrier ≤ K_unif * volume.real (T j).carrier := fun i _ j _ =>
      calc volume.real (T i).carrier
          ≤ c_up * δ ^ (Module.finrank ℝ E - 1) :=
            by
              have hRHS_fin :
                  (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
                      (δNN : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
                ENNReal.mul_ne_top ENNReal.coe_ne_top
                  (ENNReal.pow_ne_top ENNReal.coe_ne_top)
              have hreal := ENNReal.toReal_mono hRHS_fin
                (Tube.volume_le (by exact_mod_cast hδ_lt_one.le) (T i).toTube)
              simpa [MeasureTheory.Measure.real, hc_up_def, hδ_def,
                ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
        _ = K_unif * (c_low * δ ^ (Module.finrank ℝ E - 1)) := by
              rw [hK_unif_def, ← mul_assoc, div_mul_cancel₀ _ hc_low_pos.ne']
        _ ≤ K_unif * volume.real (T j).carrier :=
              mul_le_mul_of_nonneg_left (hT_vol_lb_real j) hK_unif_pos.le
    have htest_real : ∃ KTest : Finset (ConvexSpaceBody E),
        (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
        (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
        ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)).toReal ≤
        Ctest * (densityIn u (fun i ↦ (T i).toConvexSpaceBody) K).toReal := by
      obtain ⟨KTest, hKT_sub, hKT_card, hKT_test⟩ :=
        exists_localized_finite_test_family_maxDensity.{u, _} (E := E) (r := δNN) (R := 1)
          hδNN_pos (by exact_mod_cast hδ_lt_one.le) le_rfl
      refine ⟨KTest, ?_, ?_, fun u _hu => ?_⟩
      · -- The test bodies sit in `B(0,1)`, hence a fortiori in its unit thickening.
        intro K hK x hx
        exact Metric.self_subset_cthickening _
          (by simpa only [NNReal.coe_one, ConvexSpaceBody.closedUnitBall_carrier]
            using hKT_sub K hK hx)
      · -- Absorb the multiplicative constant `Ctest` into the padded exponent `Mtest = M + 1`.
        set M : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) with hM_def
        have hcard_real : (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := by
          rw [NNReal.one_rpow, mul_one] at hKT_card
          rw [hCtest_def, hδ_def]
          exact_mod_cast hKT_card
        have hCtest_le : Ctest ≤ δ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ_pos]
          calc Ctest * δ = δ * Ctest := mul_comm _ _
            _ ≤ 1 := ((lt_div_iff₀ hCtest_pos).mp hδ_lt_invCtest).le
        have hsplit : δ ^ (-Mtest) = δ ^ (-M) * δ ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hδ_pos, hMtest_def]
          congr 1
          ring
        calc (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := hcard_real
          _ ≤ δ ^ (-1 : ℝ) * δ ^ (-M) :=
              mul_le_mul_of_nonneg_right hCtest_le (Real.rpow_nonneg hδ_pos.le _)
          _ = δ ^ (-M) * δ ^ (-1 : ℝ) := mul_comm _ _
          _ = δ ^ (-Mtest) := hsplit.symm
      · obtain ⟨K, hK_mem, hK_le⟩ :=
          hKT_test u (fun i ↦ (T i).toConvexSpaceBody)
            (fun i _ => by simpa only [NNReal.coe_one] using hB i)
            (fun i _ => by
              rw [Metric.ethickness.scale_eq]
              exact (T i).toTube.le_ethickness_finrank_sub_one)
        refine ⟨K, hK_mem, ?_⟩
        have h_ennr := ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (densityIn_ne_top _ _ _)) hK_le
        rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ← hCtest_def] at h_ennr
    obtain ⟨s', hs'_sub, hs'_ne, hs'_card_ub, hs'_KT, hs'_full, hs'_mu⟩ :=
        exists_random_subset E (η₁ := η_K / 2) (c := 2 * η_K) (half_pos hη_K_pos)
          (by linarith) s T hB (Finset.nonempty_iff_ne_empty.mpr hs) hδ_pos
          K_unif hK_unif_pos hT_unif hδ_small_K
          Mtest Ctest hMtest_pos hCtest_pos htest_real
          hδ_small_b hδ5_c hδ5_b hfull
    have hηK_le_half : η_K ≤ η1 / 2 := min_le_left _ _
    have hs'_KT' : IsKatzTao s' W ((δNN : ENNReal) ^ (-η1)) :=
      hs'_KT.mono <| by
        rw [ennreal_coe_nnreal_rpow hδ_pos]
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith))
    have hs'_full' : (δNN : NNReal) ^ η1 ≤ ShadedBody.fullness s' V := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      calc (δ : ℝ) ^ η1
          ≤ (δ : ℝ) ^ η_K := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
            (by linarith [hη_K_pos])
        _ = (δ : ℝ) ^ (2 * (η_K / 2)) := by congr 1; ring
        _ ≤ _ := hs'_full
    -- ENNReal multiplicity bound for `s'`, obtained from `hδ_KKT`.
    have hmu_s'_le_enn : ShadedBody.multiplicity s' V ≤
        (δNN : ENNReal) ^ (-(ε / 4)) * (s'.card : ENNReal) ^ β := by
      rw [ShadedBody.multiplicity_le_iff, mul_assoc]
      have : ∀ i ∈ s', (T i).carrier ⊆ Metric.closedBall 0 1 := fun i hi => hB i
      exact (hδ_KKT s' T this hs'_KT' hs'_full').trans_eq (mul_assoc _ _ _)
    -- The ℝ-valued multiplicity bound for `s'` (derived by `.toReal`).
    have h_mu_s'_R_le : multiplicityRLocal E s' V ≤
        δ ^ (-(ε / 4)) * (s'.card : ℝ) ^ β := by
      have h_top : (δNN : ENNReal) ^ (-(ε / 4)) * (s'.card : ENNReal) ^ β ≠ ⊤ :=
        ENNReal.mul_ne_top (by rw [ennreal_coe_nnreal_rpow hδ_pos]; exact ENNReal.ofReal_ne_top)
          (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))
      simpa [multiplicityRLocal, ENNReal.toReal_mul, ennreal_coe_nnreal_rpow_toReal hδ_pos,
        ← ENNReal.toReal_rpow] using ENNReal.toReal_mono h_top hmu_s'_le_enn
    have h_mu_s_R_le : multiplicityRLocal E s V ≤
        δ ^ (-ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
      calc multiplicityRLocal E s V
        _ ≤ δ ^ (-(2 * η_K)) * Δ * multiplicityRLocal E s' V := hs'_mu
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-(ε / 4)) * (s'.card : ℝ) ^ β) :=
              mul_le_mul_of_nonneg_left
                h_mu_s'_R_le
                (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-(ε / 4)) * (2 * (s.card : ℝ) * Δ⁻¹) ^ β) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg _) hs'_card_ub hβ_0)
                (Real.rpow_nonneg hδ_pos.le _))
              (mul_nonneg (Real.rpow_nonneg hδ_pos.le _) ENNReal.toReal_nonneg)
        _ ≤ δ ^ (-(2 * η_K)) * Δ * (δ ^ (-(ε / 2)) * ((s.card : ℝ) * Δ⁻¹) ^ β) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
                ENNReal.toReal_nonneg)
              rw [show (2 : ℝ) * s.card * Δ⁻¹ = (2 : ℝ) * (s.card * Δ⁻¹) from by ring,
                  Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
                (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg)),
                show δ ^ (-(ε / 4)) * ((2 : ℝ) ^ β * (s.card * Δ⁻¹) ^ β)
                  = (δ ^ (-(ε / 4)) * (2 : ℝ) ^ β) * (s.card * Δ⁻¹) ^ β from by ring]
              exact mul_le_mul_of_nonneg_right
                (calc δ ^ (-(ε / 4)) * (2 : ℝ) ^ β
                    ≤ δ ^ (-(ε / 4)) * δ ^ (-(ε / 4)) :=
                      mul_le_mul_of_nonneg_left h_2β_le (Real.rpow_nonneg hδ_pos.le _)
                  _ = δ ^ (-(ε / 2)) := by rw [← Real.rpow_add hδ_pos]; congr 1; ring)
                (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
                  (inv_nonneg.mpr ENNReal.toReal_nonneg)) _)
        _ = δ ^ (-(2 * η_K + ε / 2)) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              rw [Real.mul_rpow (Nat.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg),
              show (Δ⁻¹ : ℝ) ^ β = Δ ^ (-β) from by rw [Real.inv_rpow ENNReal.toReal_nonneg,
                  ← Real.rpow_neg ENNReal.toReal_nonneg],
              show δ ^ (-(2 * η_K)) * Δ * (δ ^ (-(ε / 2)) * ((s.card) ^ β * Δ ^ (-β)))
                      = (δ ^ (-(2 * η_K)) * δ ^ (-(ε / 2))) * (Δ * Δ ^ (-β)) * (s.card) ^ β
                      from by ring,
               ← Real.rpow_add hδ_pos,
               show -(2 * η_K) + -(ε / 2) = -(2 * η_K + ε / 2) from by ring,
              show Δ * Δ ^ (-β) = Δ ^ (1 : ℝ) * Δ ^ (-β) from by rw [Real.rpow_one],
                ← Real.rpow_add hΔ_pos, show (1 : ℝ) + -β = 1 - β from by ring]
        _ ≤ δ ^ (-ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              exact Real.rpow_le_rpow_of_exponent_ge hδ_pos (le_of_lt hδ_lt_one)
                (by linarith [min_le_right (η1 / 2) (ε / 8)])
    -- Lift the real-valued bound to ENNReal and match the goal.
    have h_mu_ne_top : ShadedBody.multiplicity s V ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (ShadedBody.multiplicity_le_card s V)
    refine ((ENNReal.le_ofReal_iff_toReal_le h_mu_ne_top
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))).2 h_mu_s_R_le).trans ?_
    have h_card_eq : ENNReal.ofReal ((s.card : ℝ) ^ β) = (s.card : ENNReal) ^ β := by
      rw [show ((s.card : ℝ) ^ β : ℝ) = ((s.card : ENNReal) ^ β).toReal from by
            rw [← ENNReal.toReal_rpow]; simp,
          ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hβ_0 (ENNReal.natCast_ne_top _))]
    rw [show (δ ^ (-ε) * Δ ^ (1 - β) * (s.card : ℝ) ^ β : ℝ)
          = δ ^ (-ε) * (Δ ^ (1 - β) * (s.card : ℝ) ^ β) from by ring,
        ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _),
        ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
        ← ennreal_coe_nnreal_rpow hδ_pos,
        show ENNReal.ofReal (Δ ^ (1 - β)) = (maxDensity s W) ^ (1 - β) from by
          rw [← ENNReal.ofReal_rpow_of_pos hΔ_pos, hΔ_def,
              ENNReal.ofReal_toReal (maxDensity_ne_top s W)],
        h_card_eq, mul_assoc]


/-- **The cardinality-efficient subfamily of GWZ Lemma 3.7, exported.**

`Kakeya.exists_random_subset` (`Kakeya/Probability.lean`) is GWZ's *"choose a random subset
`T′ ⊂ T` with cardinality `|T|/Δmax(T)`"*.  It is consumed only inside the proof of
`Kakeya.KatzTaoEstimate.multiplicity_bound` below, whose conclusion mentions neither the subfamily
nor its cardinality, so the construction has been unavailable to any other consumer.

This theorem re-exports it, with the hypothesis discharge of `multiplicity_bound` reproduced
verbatim: the uniform tube-volume comparison, the localized finite test family, and the three
smallness thresholds on `δ`, all of which hold for **any** family of shaded `δ`-tubes in the unit
ball — which is exactly the fine family of GWZ Proposition 6.6(B).

The four clauses are what a consumer needs:

* `s'` is **cardinality-efficient**: `|s'| ≤ 2 |s| / Δmax(s)`;
* `s'` is **Katz--Tao at a sub-polynomial constant**, `δ ^ (-ηKT)`;
* `s'` **retains fullness**, `δ ^ ηKT ≤ λ(s')`;
* the **multiplicity transfers** at loss `δ ^ (-ε) · Δmax(s)`.

Composed with `Kakeya.multiplicity_bound_transfer_of_cardEfficient`
(`Kakeya/DimensionThree/Plank/PartBFineEssDistinct.lean`) the `Δmax(s)` of the last clause and the
`Δmax(s) ^ (-β)` of the first combine to `Δmax(s) ^ (1 - β)` — the factor GWZ 6.6(B) already
carries — so a `6.6(B)`-shaped bound for `s'` transfers to `s` with no density hypothesis and no
essential-distinctness hypothesis anywhere.

Nothing in this file is altered: `Kakeya.exists_random_subset` and
`Kakeya.KatzTaoEstimate.multiplicity_bound` keep their statements and proofs. -/
theorem KatzTaoEstimate.exists_cardEfficient_subfamily [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ ηKT > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η →
      s ≠ ∅ →
      ∃ s' ⊆ s, s'.Nonempty ∧
        (s'.card : ℝ) ≤ 2 * (s.card : ℝ) *
          ((maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal)⁻¹ ∧
        IsKatzTao s' (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηKT)) ∧
        (δ : NNReal) ^ ηKT ≤ ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) ∧
        multiplicityRLocal E s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ℝ) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)).toReal *
            multiplicityRLocal E s' (fun i ↦ (T i).toShadedBody) := by
  intro ε hε
  obtain ⟨η1, hη1_pos, hKKT⟩ := h (ε / 4) (by linarith)
  set η_K := min (η1 / 2) (ε / 8) with hη_K_def
  have hη_K_pos : 0 < η_K := lt_min (half_pos hη1_pos) (by linarith)
  refine ⟨η_K / 2, half_pos hη_K_pos, η1, hη1_pos, ?_⟩
  set c_low : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hc_up_def
  set K_unif : ℝ := c_up / c_low with hK_unif_def
  have hK_unif_pos : 0 < K_unif := div_pos (NNReal.coe_pos.mpr (Tube.volume_le.C_pos _)) hc_low_pos
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- Density test family constants: the discretization constants of
  -- `exists_localized_finite_test_family_maxDensity` at radius `R = 1`. The exponent is padded by
  -- `+1` so that the multiplicative constant `Ctest` can be absorbed into `δ ^ (-Mtest)` for
  -- small `δ` (the `hδ_lt_invCtest` conjunct below).
  set Ctest : ℝ := (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
    with hCtest_def
  set Mtest : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) + 1
    with hMtest_def
  have hCtest_pos : 0 < Ctest :=
    NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
  have hMtest_pos : 0 < Mtest := by
    rw [hMtest_def]
    linarith [exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)]
  filter_upwards [hKKT,
      (nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
        (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))),
      (nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ)
        (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ)),
      nnreal_eventually_of_real_eventually
        (absorb_two_rpow_le_rpow_neg β (ε := ε / 4) (by linarith)),
      nnreal_eventually_of_real_eventually
        (absorb_four_K4_le_rpow_neg (K := K_unif) (η := η_K / 2) hK_unif_pos (half_pos hη_K_pos)),
      nnreal_eventually_of_real_eventually
        (absorb_log_le_rpow_neg (C := Ctest) (M := 8 * Mtest + 8) (η := η_K)
          hCtest_pos (by linarith) hη_K_pos),
      nnreal_eventually_of_real_eventually
        (absorb_exp_K_le_div_five (K := K_unif) (η := η_K) hK_unif_pos hη_K_pos),
      nnreal_eventually_of_real_eventually absorb_delta_le_div_five,
      nnreal_eventually_of_real_eventually (p := fun δ => δ < 1 / Ctest)
        (nhdsWithin_le_nhds (Iio_mem_nhds (one_div_pos.mpr hCtest_pos)))]
    with δNN hδ_KKT hδ_lt_one hδ_pos h_2β_le hδ_small_K hδ_small_b
         hδ5_c hδ5_b hδ_lt_invCtest
  set δ : ℝ := (δNN : ℝ) with hδ_def
  have hδNN_pos : (0 : NNReal) < δNN := by exact_mod_cast hδ_pos
  intro ι s T hB hfull hs
  set W := fun i ↦ (T i).toConvexSpaceBody with hW
  set V := fun i ↦ (T i).toShadedBody with hV
  set Δ : ℝ := (maxDensity s W).toReal with hΔ_def
  have hT_vol_lb_real : ∀ i,
      c_low * δ ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier :=
    fun i => tube_le_volume_real E (T i)
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  have hvol_pos : 0 < volume (W i₀).carrier :=
    (ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le
      (mul_pos hc_low_pos (pow_pos hδ_pos _)) (hT_vol_lb_real i₀))).1
  have hΔ_pos : 0 < Δ :=
    ENNReal.toReal_pos
      (zero_lt_one.trans_le (one_le_maxDensity ⟨i₀, hi₀, hvol_pos⟩)).ne'
      (maxDensity_ne_top s W)
  have hT_unif : ∀ i ∈ s, ∀ j ∈ s,
      volume.real (T i).carrier ≤ K_unif * volume.real (T j).carrier := fun i _ j _ =>
    calc volume.real (T i).carrier
        ≤ c_up * δ ^ (Module.finrank ℝ E - 1) :=
          by
            have hRHS_fin :
                (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
                    (δNN : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
              ENNReal.mul_ne_top ENNReal.coe_ne_top
                (ENNReal.pow_ne_top ENNReal.coe_ne_top)
            have hreal := ENNReal.toReal_mono hRHS_fin
              (Tube.volume_le (by exact_mod_cast hδ_lt_one.le) (T i).toTube)
            simpa [MeasureTheory.Measure.real, hc_up_def, hδ_def,
              ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
      _ = K_unif * (c_low * δ ^ (Module.finrank ℝ E - 1)) := by
            rw [hK_unif_def, ← mul_assoc, div_mul_cancel₀ _ hc_low_pos.ne']
      _ ≤ K_unif * volume.real (T j).carrier :=
            mul_le_mul_of_nonneg_left (hT_vol_lb_real j) hK_unif_pos.le
  have htest_real : ∃ KTest : Finset (ConvexSpaceBody E),
      (∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) ∧
      (KTest.card : ℝ) ≤ (δ : ℝ) ^ (-Mtest) ∧ ∀ u : Finset ι, u ⊆ s →
      ∃ K ∈ KTest, (maxDensity u (fun i ↦ (T i).toConvexSpaceBody)).toReal ≤
      Ctest * (densityIn u (fun i ↦ (T i).toConvexSpaceBody) K).toReal := by
    obtain ⟨KTest, hKT_sub, hKT_card, hKT_test⟩ :=
      exists_localized_finite_test_family_maxDensity.{u, _} (E := E) (r := δNN) (R := 1)
        hδNN_pos (by exact_mod_cast hδ_lt_one.le) le_rfl
    refine ⟨KTest, ?_, ?_, fun u _hu => ?_⟩
    · -- The test bodies sit in `B(0,1)`, hence a fortiori in its unit thickening.
      intro K hK x hx
      exact Metric.self_subset_cthickening _
        (by simpa only [NNReal.coe_one, ConvexSpaceBody.closedUnitBall_carrier]
          using hKT_sub K hK hx)
    · -- Absorb the multiplicative constant `Ctest` into the padded exponent `Mtest = M + 1`.
      set M : ℝ := exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) with hM_def
      have hcard_real : (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := by
        rw [NNReal.one_rpow, mul_one] at hKT_card
        rw [hCtest_def, hδ_def]
        exact_mod_cast hKT_card
      have hCtest_le : Ctest ≤ δ ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hδ_pos]
        calc Ctest * δ = δ * Ctest := mul_comm _ _
          _ ≤ 1 := ((lt_div_iff₀ hCtest_pos).mp hδ_lt_invCtest).le
      have hsplit : δ ^ (-Mtest) = δ ^ (-M) * δ ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hδ_pos, hMtest_def]
        congr 1
        ring
      calc (KTest.card : ℝ) ≤ Ctest * δ ^ (-M) := hcard_real
        _ ≤ δ ^ (-1 : ℝ) * δ ^ (-M) :=
            mul_le_mul_of_nonneg_right hCtest_le (Real.rpow_nonneg hδ_pos.le _)
        _ = δ ^ (-M) * δ ^ (-1 : ℝ) := mul_comm _ _
        _ = δ ^ (-Mtest) := hsplit.symm
    · obtain ⟨K, hK_mem, hK_le⟩ :=
        hKT_test u (fun i ↦ (T i).toConvexSpaceBody)
          (fun i _ => by simpa only [NNReal.coe_one] using hB i)
          (fun i _ => by
            rw [Metric.ethickness.scale_eq]
            exact (T i).toTube.le_ethickness_finrank_sub_one)
      refine ⟨K, hK_mem, ?_⟩
      have h_ennr := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (densityIn_ne_top _ _ _)) hK_le
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ← hCtest_def] at h_ennr
  obtain ⟨s', hs'_sub, hs'_ne, hs'_card_ub, hs'_KT, hs'_full, hs'_mu⟩ :=
      exists_random_subset E (η₁ := η_K / 2) (c := 2 * η_K) (half_pos hη_K_pos)
        (by linarith) s T hB (Finset.nonempty_iff_ne_empty.mpr hs) hδ_pos
        K_unif hK_unif_pos hT_unif hδ_small_K
        Mtest Ctest hMtest_pos hCtest_pos htest_real
        hδ_small_b hδ5_c hδ5_b hfull
  have hηK_le_half : η_K ≤ η1 / 2 := min_le_left _ _
  have hs'_KT' : IsKatzTao s' W ((δNN : ENNReal) ^ (-η1)) :=
    hs'_KT.mono <| by
      rw [ennreal_coe_nnreal_rpow hδ_pos]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith))
  have hs'_full' : (δNN : NNReal) ^ η1 ≤ ShadedBody.fullness s' V := by
    rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
    calc (δ : ℝ) ^ η1
        ≤ (δ : ℝ) ^ η_K := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
          (by linarith [hη_K_pos])
      _ = (δ : ℝ) ^ (2 * (η_K / 2)) := by congr 1; ring
      _ ≤ _ := hs'_full
  refine ⟨s', hs'_sub, hs'_ne, hs'_card_ub, hs'_KT', hs'_full', ?_⟩
  have hmono : δ ^ (-(2 * η_K)) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
      (by linarith [min_le_right (η1 / 2) (ε / 8)])
  calc multiplicityRLocal E s V
      ≤ δ ^ (-(2 * η_K)) * Δ * multiplicityRLocal E s' V := hs'_mu
    _ ≤ δ ^ (-ε) * Δ * multiplicityRLocal E s' V :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmono ENNReal.toReal_nonneg)
          (multiplicityRLocal_nonneg E s' V)


/-- Blueprint `tubeCardBound`: the polynomial cardinality bound for a family of `δ`-tubes in the
unit ball, read against the maximal density rather than against the density in `B_1`, and with the
integer power rewritten as a real one. -/
private lemma card_le_maxDensity_rpow [Nontrivial E] {δ : NNReal} (hδ : δ ≠ 0)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hball : ∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) :
    (s.card : ENNReal) ≤
      (Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : ENNReal) *
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) *
        (δ : ENNReal) ^ (-((Module.finrank ℝ E : ℝ) - 1)) := by
  convert Tube.card_le_of_densityIn_le (δ := δ) (T := fun i ↦ (T i).toTube)
    hδ (fun i _ => hball i) (le_maxDensity s _ _) using 2
  rw [show (-((Module.finrank ℝ E : ℝ) - 1) : ℝ) =
      ((-(((Module.finrank ℝ E : ℕ) : ℤ) - 1) : ℤ) : ℝ) from by
        push_cast; ring, ENNReal.rpow_intCast]

/-- Blueprint `trivialMultBoundLe1`: for `0 ≤ β ≤ 1` the trivial bound `μ ≤ #s`, combined with the
cardinality bound `card_le_maxDensity_rpow`, gives the Lemma 3.7 right-hand side with the `τ`-free
loss factor `δ ^ (-n)`. -/
private lemma multiplicity_le_trivial_of_le_one [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hδC : (Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : ENNReal) + 1
      ≤ (δ : ENNReal)⁻¹)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hball : ∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) :
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(Module.finrank ℝ E : ℝ)) *
        (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  · set n : ℕ := Module.finrank ℝ E with hn_def
    set C : NNReal := Tube.card_le_of_densityIn_le.C n with hC
    set Δ := maxDensity s (fun i ↦ (T i).toConvexSpaceBody) with hΔ
    set N := (s.card : ENNReal) with hN
    have hN_card : 0 < (s.card : Nat) :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have hN_ne_zero : N ≠ 0 := by
      rw [hN]
      exact_mod_cast hN_card.ne'
    have hN_ne_top : N ≠ ⊤ := by
      rw [hN]
      exact ENNReal.natCast_ne_top s.card
    have hN_split : N = N ^ β * N ^ (1 - β) := by
      rw [← ENNReal.rpow_add β (1 - β) hN_ne_zero hN_ne_top]
      rw [show β + (1 - β) = 1 by ring]
      rw [ENNReal.rpow_one]
    have hβ1m : 0 ≤ 1 - β := by linarith
    have hβ1m_le_one : 1 - β ≤ 1 := by linarith
    have hn_pos : 0 < n := by simpa [hn_def] using Module.finrank_pos
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn_pos
      linarith
    have hδC' : ((C : ENNReal) + 1) ≤ (δ : ENNReal)⁻¹ := by
      simpa [hC, hn_def] using hδC
    have hcard_raw : (s.card : ENNReal) ≤
        (Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : ENNReal) *
          maxDensity s (fun i ↦ (T i).toConvexSpaceBody) *
          (δ : ENNReal) ^ (-((Module.finrank ℝ E : ℝ) - 1)) :=
      card_le_maxDensity_rpow (E := E) (δ := δ) hδ.ne' s T hball
    have hcard : N ≤ (C : ENNReal) * Δ * (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
      simpa [hN, hΔ, hC, hn_def] using hcard_raw
    have hCpow : (C : ENNReal) ^ (1 - β) ≤ (C : ENNReal) + 1 := by
      by_cases h1leC : 1 ≤ (C : ENNReal)
      · calc
          (C : ENNReal) ^ (1 - β) ≤ (C : ENNReal) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le h1leC hβ1m_le_one
          _ = (C : ENNReal) := ENNReal.rpow_one _
          _ ≤ (C : ENNReal) + 1 := le_self_add
      · have hCle1 : (C : ENNReal) ≤ 1 := le_of_not_ge h1leC
        calc
          (C : ENNReal) ^ (1 - β) ≤ (C : ENNReal) ^ (0 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hCle1 hβ1m
          _ = 1 := by rw [ENNReal.rpow_zero]
          _ ≤ (C : ENNReal) + 1 := by exact le_add_of_nonneg_left bot_le
    have hδpow_le : ((δ : ENNReal) ^ (-((n : ℝ) - 1))) ^ (1 - β) ≤
        (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
      rw [← ENNReal.rpow_mul]
      have h_exp_ge : (-((n : ℝ) - 1)) ≤ (-((n : ℝ) - 1)) * (1 - β) := by
        rw [show (-((n : ℝ) - 1)) * (1 - β) = (-((n : ℝ) - 1)) + ((n : ℝ) - 1) * β by ring]
        exact le_add_of_nonneg_right (mul_nonneg hn1 hβ_0)
      exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1.le) h_exp_ge
    have h_δC_mul : ((C : ENNReal) + 1) * (δ : ENNReal) ^ (-((n : ℝ) - 1)) ≤
        (δ : ENNReal) ^ (-(n : ℝ)) := by
      have hδC'' : ((C : ENNReal) + 1) ≤ (δ : ENNReal) ^ (-(1 : ℝ)) := by
        simpa [ENNReal.rpow_neg, ENNReal.rpow_one] using hδC'
      calc
        ((C : ENNReal) + 1) * (δ : ENNReal) ^ (-((n : ℝ) - 1))
            ≤ (δ : ENNReal) ^ (-(1 : ℝ)) * (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
                exact mul_le_mul_of_nonneg_right hδC'' bot_le
        _ = (δ : ENNReal) ^ (-(n : ℝ)) := by
                rw [← ENNReal.rpow_add (-(1 : ℝ)) (-((n : ℝ) - 1))
                  (by exact_mod_cast hδ.ne') (by simp)]
                rw [show (-(1 : ℝ)) + -((n : ℝ) - 1) = -(n : ℝ) by ring]
    have hNpow_le : N ^ (1 - β) ≤ (δ : ENNReal) ^ (-(n : ℝ)) * Δ ^ (1 - β) := by
      calc
        N ^ (1 - β)
            ≤ ((C : ENNReal) * Δ * (δ : ENNReal) ^ (-((n : ℝ) - 1))) ^ (1 - β) :=
              ENNReal.rpow_le_rpow hcard hβ1m
        _ = (C : ENNReal) ^ (1 - β) * Δ ^ (1 - β) *
              ((δ : ENNReal) ^ (-((n : ℝ) - 1))) ^ (1 - β) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m]
        _ ≤ ((C : ENNReal) + 1) * Δ ^ (1 - β) *
              ((δ : ENNReal) ^ (-((n : ℝ) - 1))) ^ (1 - β) := by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_right hCpow bot_le
        _ ≤ ((C : ENNReal) + 1) * Δ ^ (1 - β) * (δ : ENNReal) ^ (-((n : ℝ) - 1)) := by
              exact mul_le_mul_of_nonneg_left hδpow_le (mul_nonneg bot_le bot_le)
        _ ≤ (δ : ENNReal) ^ (-(n : ℝ)) * Δ ^ (1 - β) := by
              have hcommδ : (δ : ENNReal) ^ (-((n : ℝ) - 1)) * ((C : ENNReal) + 1) ≤
                  (δ : ENNReal) ^ (-(n : ℝ)) := by
                simpa [mul_comm] using h_δC_mul
              have hstep : Δ ^ (1 - β) * (δ ^ (-((n : ℝ) - 1)) * ((C : ENNReal) + 1)) ≤
                  Δ ^ (1 - β) * (δ : ENNReal) ^ (-(n : ℝ)) :=
                mul_le_mul_of_nonneg_left hcommδ bot_le
              simpa [mul_assoc, mul_comm, mul_left_comm] using hstep
    calc
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤ N :=
        ShadedBody.multiplicity_le_card s (fun i ↦ (T i).toShadedBody)
      _ = N ^ β * N ^ (1 - β) := hN_split
      _ ≤ N ^ β * ((δ : ENNReal) ^ (-(n : ℝ)) * Δ ^ (1 - β)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_right hNpow_le bot_le
      _ = (δ : ENNReal) ^ (-(n : ℝ)) * Δ ^ (1 - β) * N ^ β := by
          exact mul_comm _ _

/-- Blueprint `scaleCompare`: the exponent arithmetic of the Remark 3.6 dichotomy in its
large-`τ` branch, where `τ` is at least `δ ^ L` and the working exponent is `η₁ / L`. -/
private lemma rpow_scale_compare {δ τ : NNReal} (hτ : 0 < τ) (hτδ : τ ≤ δ)
    {ε η₁ L : ℝ} (hε : 0 < ε) (hη₁ : 0 < η₁) (hL : 0 < L) (hcase : δ ^ L ≤ τ) :
    (δ : ENNReal) ^ η₁ ≤ (τ : ENNReal) ^ (η₁ / L) ∧
      (δ : ENNReal) ^ (-ε) ≤ (τ : ENNReal) ^ (-ε) := by
  constructor
  · conv_lhs => rw [show η₁ = L * (η₁ / L) by field_simp [ne_of_gt hL],
        ENNReal.rpow_mul]
    have hcase' : (δ : ENNReal) ^ L ≤ (τ : ENNReal) := by
      rw [← ENNReal.coe_rpow_of_nonneg _ hL.le, ENNReal.coe_le_coe]
      exact hcase
    exact ENNReal.rpow_le_rpow hcase' (by positivity)
  · rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr
      (ENNReal.rpow_le_rpow (by exact_mod_cast hτδ) hε.le)

/-- [GWZ, Remark 3.6] applied to [GWZ, Lemma 3.7]: the multiplicity bound of Lemma 3.7 with the
analytic scale decoupled from the geometric one.  The tubes still have radius `δ`, but both the
fullness hypothesis and the loss factor are measured at an auxiliary scale `τ ≤ δ`.

As in `Kakeya.KatzTaoEstimate.generalize`, the proof is a dichotomy on `τ` against a power of `δ`
determined by `ε`: for `τ` not too small the ordinary Lemma 3.7 applies and `τ ≤ δ` upgrades its
loss, while for very small `τ` the factor `τ ^ (-ε)` alone dominates the trivial bound
`multiplicity ≤ #s` through the polynomial cardinality control
`Kakeya.Tube.card_le_of_densityIn_le`. -/
theorem KatzTaoEstimate.multiplicity_bound_generalize [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β)
    (h : KatzTaoEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  classical
  intro ε hε
  obtain ⟨η₁, hη₁, hev⟩ := KatzTaoEstimate.multiplicity_bound (E := E) hβ_0 h ε hε
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn : 0 < n := by
    rw [hn_def]
    exact Module.finrank_pos
  set C : NNReal := Tube.card_le_of_densityIn_le.C n with hC_def
  set L : ℝ := (n : ℝ) / ε with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def]
    positivity
  have hL_ε : L * ε = (n : ℝ) := by
    rw [hL_def]
    field_simp [ne_of_gt hε]
  set η : ℝ := η₁ / L with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    positivity
  refine ⟨η, hη_pos, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one),
    Ioo_mem_nhdsGT (show (0 : NNReal) < ((C : NNReal) + 1)⁻¹ from by positivity)]
    with δ hδ_hev ⟨hδ0, hδ1⟩ ⟨_, hδ_lt_invC⟩
  intro τ hτ_pos hτ_le_δ ι s T hball hfull
  by_cases hcase : δ ^ L ≤ τ
  · have h_scale := rpow_scale_compare hτ_pos hτ_le_δ hε hη₁ hL_pos hcase
    have h_δτ_full : (δ : NNReal) ^ η₁ ≤ (τ : NNReal) ^ η := by
      rw [hη_def, ← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg _ hη₁.le,
        ENNReal.coe_rpow_of_nonneg _ hη_pos.le]
      exact h_scale.1
    have hfull_real : (δ : ℝ) ^ η₁ ≤
        (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) := by
      rw [← NNReal.coe_rpow]
      exact_mod_cast (le_trans h_δτ_full hfull)
    have h_bound : multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
          (s.card : ENNReal) ^ β :=
      hδ_hev s T hball hfull_real
    calc
      multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
            (s.card : ENNReal) ^ β := h_bound
      _ ≤ (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
            (s.card : ENNReal) ^ β := by
          exact mul_le_mul' (mul_le_mul' h_scale.2 le_rfl) le_rfl
  · push Not at hcase
    have h_τ_le_δL_enn : (τ : ENNReal) ≤ (δ : ENNReal) ^ L := by
      rw [← ENNReal.coe_rpow_of_nonneg _ hL_pos.le]
      exact ENNReal.coe_le_coe.mpr hcase.le
    have h_τ_le_δL_ε : (τ : ENNReal) ^ ε ≤ (δ : ENNReal) ^ (L * ε) := by
      calc
        (τ : ENNReal) ^ ε ≤ ((δ : ENNReal) ^ L) ^ ε :=
          ENNReal.rpow_le_rpow h_τ_le_δL_enn hε.le
        _ = (δ : ENNReal) ^ (L * ε) := by rw [← ENNReal.rpow_mul]
    have hδτ : (δ : ENNReal) ^ (-(n : ℝ)) ≤ (τ : ENNReal) ^ (-ε) := by
      rw [← hL_ε, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr h_τ_le_δL_ε
    have hδC : (Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : ENNReal) + 1 ≤
        (δ : ENNReal)⁻¹ := by
      have hδC' : (Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : NNReal) + 1 ≤ δ⁻¹ := by
        have hδ_lt_invC_real : (δ : ℝ) < (((C : NNReal) + 1 : NNReal) : ℝ)⁻¹ := by
          exact_mod_cast hδ_lt_invC
        have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
        have hC_real_pos : (0 : ℝ) <
            ((Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : NNReal) + 1 : ℝ) := by
              positivity
        have h_mul_lt : (δ : ℝ) *
            ((Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : NNReal) + 1 : ℝ) < 1 := by
          rw [inv_eq_one_div] at hδ_lt_invC_real
          exact (lt_div_iff₀ hC_real_pos).mp hδ_lt_invC_real
        have h_mul_lt' : ((Tube.card_le_of_densityIn_le.C (Module.finrank ℝ E) : NNReal) + 1 : ℝ) *
            (δ : ℝ) < 1 := by
          simpa [mul_comm] using h_mul_lt
        rw [inv_eq_one_div]
        exact ((lt_div_iff₀ hδ_real_pos).mpr h_mul_lt').le
      rw [← ENNReal.coe_inv (by exact_mod_cast hδ0.ne')]
      exact ENNReal.coe_le_coe.mpr hδC'
    rcases le_total β 1 with hβ_le | hβ_ge
    · have h_triv : multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-(Module.finrank ℝ E : ℝ)) *
            (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
            (s.card : ENNReal) ^ β :=
        multiplicity_le_trivial_of_le_one (E := E) hβ_0 hβ_le hδ0 hδ1 hδC s T hball
      calc
        multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(Module.finrank ℝ E : ℝ)) *
              (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
              (s.card : ENNReal) ^ β := h_triv
        _ ≤ (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
              (s.card : ENNReal) ^ β := by
            exact mul_le_mul' (mul_le_mul' (by simpa [hn_def] using hδτ) le_rfl) le_rfl
    · have h_triv : multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) * (s.card : ENNReal) ^ β :=
        multiplicity_le_trivial_of_one_le (E := E) hβ_ge s
          (fun i ↦ (T i).toShadedBody) (fun i ↦ (T i).toConvexSpaceBody)
      have hτ_lt_one : τ < 1 := lt_of_le_of_lt hτ_le_δ hδ1
      have h_one_le : (1 : ENNReal) ≤ (τ : ENNReal) ^ (-ε) := by
        rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
        exact ENNReal.rpow_le_one (by exact_mod_cast hτ_lt_one.le) hε.le
      calc
        multiplicity s (fun i ↦ (T i).toShadedBody)
          ≤ (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) * (s.card : ENNReal) ^ β :=
            h_triv
        _ = 1 * ((maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
              (s.card : ENNReal) ^ β) := by
            rw [one_mul]
        _ ≤ (τ : ENNReal) ^ (-ε) *
              ((maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
                (s.card : ENNReal) ^ β) := by
            exact mul_le_mul' h_one_le le_rfl
        _ = (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
              (s.card : ENNReal) ^ β := by rw [mul_assoc]

end KatzTaoEstimate

section FrostmanEstimate

universe v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The partial Frostman estimate at exponent `β`. -/
def FrostmanEstimate (β : ℝ) : Prop := ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall (δ ^ (- η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        δ ^ (-ε - 2 * β) * (s.card * δ ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)

section
variable {E}

/-- **Absorbing a constant into a subpolynomial loss.**  Any positive real constant `C` is
dominated by `δ ^ (-a)` once `δ` is below a threshold depending only on `C` and `a > 0`.
This is the numerical step that lets a dimensional constant be paid for by the `δ ^ (-ε)`
loss in `Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`; compare the inlined
version at `Kakeya.KatzTaoEstimate.generalize`. -/
theorem exists_threshold_ofReal_le_rpow {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ < δ₀ →
      ENNReal.ofReal C ≤ (δ : ENNReal) ^ (-a) := by
  -- Choose δ₀ : NNReal with (δ₀ : ℝ) = (1 / C) ^ (1 / a).
  have hCinv_nonneg : 0 ≤ 1 / C := by positivity
  set r : ℝ := (1 / C) ^ (1 / a) with hr_def
  have hr_nonneg : 0 ≤ r := by
    rw [hr_def]
    exact Real.rpow_nonneg hCinv_nonneg _
  let δ₀ : NNReal := ⟨r, hr_nonneg⟩
  refine ⟨δ₀, ?_, ?_⟩
  · have h0 : 0 < (1 / C) ^ (1 / a) := Real.rpow_pos_of_pos (by positivity : 0 < 1 / C) (1 / a)
    have hδ₀_real_pos : (0 : ℝ) < (δ₀ : ℝ) := by
      rw [show (δ₀ : ℝ) = r from rfl]
      rw [hr_def]
      exact h0
    exact NNReal.coe_lt_coe.mp hδ₀_real_pos
  · intro δ hδ hδlt
    have hδ_real_pos : 0 < (δ : ℝ) := hδ
    have hδ_real_nonneg : 0 ≤ (δ : ℝ) := hδ_real_pos.le
    have hδ_le_r : (δ : ℝ) ≤ r := by
      exact_mod_cast hδlt.le
    have hpow_le : (δ : ℝ) ^ a ≤ r ^ a := Real.rpow_le_rpow hδ_real_nonneg hδ_le_r ha.le
    have hra : r ^ a = 1 / C := by
      rw [hr_def, ← Real.rpow_mul hCinv_nonneg]
      have hmul : (1 / a) * a = 1 := by field_simp [ha.ne']
      rw [hmul, Real.rpow_one]
    have hx_pos : 0 < (δ : ℝ) ^ a := Real.rpow_pos_of_pos hδ_real_pos a
    have hx_le_invC : (δ : ℝ) ^ a ≤ 1 / C := hpow_le.trans (le_of_eq hra)
    have hC_le_real : C ≤ (δ : ℝ) ^ (-a) := by
      rw [Real.rpow_neg hδ_real_nonneg]
      rw [← one_div]
      rw [le_div_iff₀ hx_pos]
      calc
        C * (δ : ℝ) ^ a ≤ C * (1 / C) := mul_le_mul_of_nonneg_left hx_le_invC hC.le
        _ = 1 := by field_simp [hC.ne']
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hδ_real_pos]
    exact ENNReal.ofReal_le_ofReal hC_le_real

/-- **The bracket bound.**  The bracket `B = |𝕋| · δ ^ (n - 1)` appearing on the right-hand
side of `Kakeya.FrostmanEstimate` is at most `C(n) · δ ^ (-(n + 1))` for any family of
pairwise essentially distinct `δ`-tubes contained in the closed unit ball, where `C(n)` is
the crude counting constant `Tube.card_le_of_EssDistinct.C n`.

This is the only bound on `B` available to `Kakeya.FrostmanEstimate.mono`; the sharper
density count `Kakeya.card_familyIn_le` is circular there, as the blueprint note
`note:frostmanEstimateMono` explains.  The exponent `-(n + 1)` is what forces the dimension
hypothesis `Module.finrank ℝ E ≤ 3` on that lemma. -/
theorem FrostmanEstimate.bracket_le [Nontrivial E] {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) :
    (s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)
      ≤ ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E))
        * (δ : ENNReal) ^ (-((Module.finrank ℝ E : ℝ) + 1)) := by
  set n := Module.finrank ℝ E
  have hn_pos : 0 < n := Module.finrank_pos
  have hn1 : 1 ≤ n := by omega
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := hδ
  have hδ_ne_zero : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ.ne.symm
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set C := Tube.card_le_of_EssDistinct.C n
  have hC_nonneg : 0 ≤ C := by
    have hC_pos : 0 < C := Tube.card_le_of_EssDistinct.C_pos
    exact hC_pos.le
  -- Step 1: get the ℝ inequality from card_le_of_EssDistinct
  have hcard_real : (s.card : ℝ) ≤ C * (1 / (δ : ℝ)) ^ (2 * n) :=
    Tube.card_le_of_EssDistinct hδ 1 s (fun i => (T i).toTube) hball hED
  -- Step 2: algebra to rewrite (1/(δ:ℝ)) ^ (2*n) = (δ : ℝ) ^ (-(2*(n : ℝ)))
  have h_eq_real : (1 / (δ : ℝ)) ^ (2 * n) = (δ : ℝ) ^ (-(2 * (n : ℝ))) := by
    rw [one_div, inv_pow]
    -- goal: (δ ^ (2 * n))⁻¹ = δ ^ (-(2 * (n : ℝ)))
    rw [← Real.rpow_natCast (δ : ℝ) (2 * n), ← Real.rpow_neg hδ_pos_real.le]
    push_cast; ring
  -- Step 3: combine to get (s.card : ℝ) ≤ C * (δ : ℝ) ^ (-(2*(n : ℝ)))
  have hcard_real' : (s.card : ℝ) ≤ C * (δ : ℝ) ^ (-(2 * (n : ℝ))) :=
    calc
      (s.card : ℝ) ≤ C * (1 / (δ : ℝ)) ^ (2 * n) := hcard_real
      _ = C * (δ : ℝ) ^ (-(2 * (n : ℝ))) := by rw [h_eq_real]
  -- Step 4: convert to ENNReal
  have hcard_enn : (s.card : ENNReal) ≤ ENNReal.ofReal C * (δ : ENNReal) ^ (-(2 * (n : ℝ))) := by
    have htemp : ENNReal.ofReal (s.card : ℝ) ≤ ENNReal.ofReal (C * (δ : ℝ) ^ (-(2 * (n : ℝ)))) :=
      ENNReal.ofReal_le_ofReal hcard_real'
    rw [ENNReal.ofReal_natCast] at htemp
    rw [ENNReal.ofReal_mul hC_nonneg] at htemp
    rw [← ENNReal.ofReal_rpow_of_pos hδ_pos_real] at htemp
    -- now `htemp` bounds `s.card` by
    -- `ENNReal.ofReal C * (ENNReal.ofReal (δ : ℝ)) ^ (-(2 * (n : ℝ)))`;
    -- note `ENNReal.ofReal (δ : ℝ) = (δ : ENNReal)`
    simpa [ENNReal.ofReal_coe_nnreal] using htemp
  -- Step 5: convert (δ : ENNReal) ^ (n-1) (natural power) to real exponent
  have h_nat_to_real : (δ : ENNReal) ^ (n - 1) = (δ : ENNReal) ^ ((n : ℝ) - 1) := by
    rw [← ENNReal.rpow_natCast, Nat.cast_sub hn1, Nat.cast_one]
  -- Step 6: combine exponents using rpow_add
  have h_exp : (δ : ENNReal) ^ (-(2 * (n : ℝ))) * (δ : ENNReal) ^ ((n : ℝ) - 1)
      = (δ : ENNReal) ^ (-((n : ℝ) + 1)) := by
    rw [← ENNReal.rpow_add (-(2 * (n : ℝ))) ((n : ℝ) - 1) hδ_ne_zero hδ_ne_top]
    ring_nf
  -- Step 7: final calculation
  have hAleqB : (s.card : ENNReal) * (δ : ENNReal) ^ (n - 1) ≤
      (ENNReal.ofReal C * (δ : ENNReal) ^ (-(2 * (n : ℝ)))) * (δ : ENNReal) ^ (n - 1) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_right hcard_enn ((δ : ENNReal) ^ (n - 1))
  have hBeqC : (ENNReal.ofReal C * (δ : ENNReal) ^ (-(2 * (n : ℝ)))) * (δ : ENNReal) ^ (n - 1) =
      ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E))
        * (δ : ENNReal) ^ (-((Module.finrank ℝ E : ℝ) + 1)) := by
    calc
      (ENNReal.ofReal C * (δ : ENNReal) ^ (-(2 * (n : ℝ)))) * (δ : ENNReal) ^ (n - 1)
          = (ENNReal.ofReal C * (δ : ENNReal) ^ (-(2 * (n : ℝ))))
              * (δ : ENNReal) ^ ((n : ℝ) - 1) := by
            rw [h_nat_to_real]
      _ = ENNReal.ofReal C
            * ((δ : ENNReal) ^ (-(2 * (n : ℝ))) * (δ : ENNReal) ^ ((n : ℝ) - 1)) := by
        ring
      _ = ENNReal.ofReal C * (δ : ENNReal) ^ (-((n : ℝ) + 1)) := by
        rw [h_exp]
      _ = ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E))
          * (δ : ENNReal) ^ (-((Module.finrank ℝ E : ℝ) + 1)) := by
        simp [C, n]
  exact hAleqB.trans hBeqC.le

end


/-- Absorbing the loss factor `(M+1) · δ^(-η)` into a single `δ^(-η₀)`, given
`(M+1) ≤ δ^(-η)` and `3η ≤ η₀` (and `0 < δ ≤ 1`). -/
lemma absorb_M_three_eta_rpow_neg {δ : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    {M_cap : ℕ} {η η₀ : ℝ}
    (hMδ : ((M_cap : ℝ) + 1) ≤ δ ^ (-η))
    (h3 : 3 * η ≤ η₀) :
    δ ^ (-η) * (((M_cap : ℝ) + 1) * δ ^ (-η)) ≤ δ ^ (-η₀) := by
  have hpow_nn : 0 ≤ δ ^ (-η) := Real.rpow_nonneg hδ_pos.le _
  have hmul_nn : 0 ≤ δ ^ (-η) * δ ^ (-η) := mul_nonneg hpow_nn hpow_nn
  calc δ ^ (-η) * (((M_cap : ℝ) + 1) * δ ^ (-η))
      = ((M_cap : ℝ) + 1) * (δ ^ (-η) * δ ^ (-η)) := by ring
    _ ≤ δ ^ (-η) * (δ ^ (-η) * δ ^ (-η)) :=
        mul_le_mul_of_nonneg_right hMδ hmul_nn
    _ = δ ^ (-η + (-η + -η)) := by
        rw [← Real.rpow_add hδ_pos, ← Real.rpow_add hδ_pos]
    _ ≤ δ ^ (-η₀) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ1 (by linarith)

/-- ENNReal↔Real bridge for the `Y`-shaped RHS of `multiplicity_bound`. -/
lemma multiplicity_bound_Y_enn_eq_ofReal
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) {ε β : ℝ} (hβ2_nn : 0 ≤ 1 - β / 2)
    (s_card n : ℕ) (h_inner_nn : 0 ≤ (s_card : ℝ) * (δ : ℝ) ^ (n - 1)) :
    (δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
        ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) =
      ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2) - 2 * β) *
        ((s_card : ℝ) * (δ : ℝ) ^ (n - 1)) ^ (1 - β / 2)) := by
  rw [ennreal_coe_nnreal_rpow hδ_pos, card_mul_δ_pow_ofReal hδ_pos s_card n,
      ENNReal.ofReal_rpow_of_nonneg h_inner_nn hβ2_nn,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _)]

/-- ENNReal↔Real bridge for the `Z`-shaped RHS of `multiplicity_bound`. -/
lemma multiplicity_bound_Z_enn_eq_ofReal
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) {CF : ENNReal} (hCF_ne_top : CF ≠ ⊤)
    {ε β : ℝ} (hβ2_nn : 0 ≤ 1 - β / 2)
    (s_card n : ℕ) (h_inner_nn : 0 ≤ (s_card : ℝ) * (δ : ℝ) ^ (n - 1)) :
    ENNReal.ofReal ((δ : ℝ) ^ (-ε) * CF.toReal ^ (1 - β / 2) * (δ : ℝ) ^ (-2 * β) *
        ((s_card : ℝ) * (δ : ℝ) ^ (n - 1)) ^ (1 - β / 2)) =
      (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
        ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
  rw [ennreal_coe_nnreal_rpow hδ_pos (-ε), ennreal_coe_nnreal_rpow hδ_pos (-2 * β),
      card_mul_δ_pow_ofReal hδ_pos s_card n,
      ENNReal.ofReal_rpow_of_nonneg h_inner_nn hβ2_nn,
      show CF ^ (1 - β / 2) = ENNReal.ofReal (CF.toReal ^ (1 - β / 2)) from by
        rw [← ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg) hβ2_nn,
            ENNReal.ofReal_toReal hCF_ne_top],
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]

/-- Fullness descent for the `ball2_version` flow: from a real-valued shade
pigeon `s_sh ≤ M · sE_sh`, fullness on `s` giving `δ^η · s_c ≤ s_sh`,
and the absorption `M ≤ δ^(η - η₀)`, derive `δ^η₀ · sE_c ≤ sE_sh`. -/
lemma fullness_descent_block
    {δ : ℝ} (hδ_pos : 0 < δ)
    {M_real η η₀ s_c sE_c sE_sh s_sh : ℝ}
    (hM_pos : 0 < M_real)
    (hM_le : M_real ≤ δ ^ (η - η₀))
    (hs_c_pos : 0 < s_c)
    (h_sE_c_le_s_c : sE_c ≤ s_c)
    (h_full_lb : δ ^ η * s_c ≤ s_sh)
    (h_shade_pig : s_sh ≤ M_real * sE_sh) :
    δ ^ η₀ * sE_c ≤ sE_sh := by
  have h_step : δ ^ η₀ * M_real ≤ δ ^ η := by
    have h1 : δ ^ η₀ * M_real ≤ δ ^ η₀ * δ ^ (η - η₀) :=
      mul_le_mul_of_nonneg_left hM_le (Real.rpow_nonneg hδ_pos.le _)
    rw [← Real.rpow_add hδ_pos] at h1
    simpa [show η₀ + (η - η₀) = η from by ring] using h1
  have h_factor_nn : 0 ≤ δ ^ η₀ * M_real :=
    mul_nonneg (Real.rpow_nonneg hδ_pos.le _) hM_pos.le
  have h_combined : δ ^ η₀ * M_real * sE_c ≤ M_real * sE_sh := calc
    δ ^ η₀ * M_real * sE_c
        ≤ δ ^ η₀ * M_real * s_c := by
          exact mul_le_mul_of_nonneg_left h_sE_c_le_s_c h_factor_nn
      _ ≤ δ ^ η * s_c := mul_le_mul_of_nonneg_right h_step hs_c_pos.le
      _ ≤ s_sh := h_full_lb
      _ ≤ M_real * sE_sh := h_shade_pig
  have h1 : M_real * (δ ^ η₀ * sE_c) ≤ M_real * sE_sh := by linarith
  exact le_of_mul_le_mul_left h1 hM_pos

/-- Fullness descent on the restricted `s'`, transferring the bound `δ^η₀ ≤
fullness s' V''` from a translation-equivalent family `V` on `s` using the
combinatorial `fullness_descent_block`. The `h_T''_*` hypotheses encode that
`V''` and `V` agree as `ShadedBody`s up to translation on `s'`. -/
lemma fullness_translate_descent
    {ι : Type*} {s s' : Finset ι} (hs'_sub : s' ⊆ s)
    (hs_ne : s.Nonempty) (hs'_ne : s'.Nonempty)
    (V V'' : ι → ShadedBody E)
    (h_T''_c : ∀ i ∈ s', volume.real (V'' i).carrier = volume.real (V i).carrier)
    (h_T''_sh : ∀ i ∈ s', volume.real (V'' i).shade = volume.real (V i).shade)
    (hT_vol_pos : ∀ i ∈ s, 0 < volume.real (V i).carrier)
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ))
    {η η₀ : ℝ} {M : ℕ} (hM_pos_real : (0 : ℝ) < M)
    (hM_abs2_δ : (M : ℝ) ≤ (δ : ℝ) ^ (η - η₀))
    (hFull : ShadedBody.fullness s V ≥ δ ^ η)
    (h_pig_shade : (∑ i ∈ s, volume.real (V i).shade) ≤
      (M : ℝ) * (∑ i ∈ s', volume.real (V i).shade)) :
    ShadedBody.fullness s' V'' ≥ δ ^ η₀ := by
  have h_sum_carrier_s_pos : 0 < (∑ i ∈ s, volume.real (V i).carrier) :=
    Finset.sum_pos (fun i hi => hT_vol_pos i hi) hs_ne
  have hsE'_c_pos : 0 < (∑ i ∈ s', volume.real (V'' i).carrier) := by
    rw [Finset.sum_congr rfl h_T''_c]
    exact Finset.sum_pos (fun i hi => hT_vol_pos i (hs'_sub hi)) hs'_ne
  have h_sE_c_le_s_c :
      (∑ i ∈ s', volume.real (V i).carrier) ≤ (∑ i ∈ s, volume.real (V i).carrier) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs'_sub (fun _ _ _ => ENNReal.toReal_nonneg)
  have h_full_lb : (δ : ℝ) ^ η *
      (∑ i ∈ s, volume.real (V i).carrier) ≤
      (∑ i ∈ s, volume.real (V i).shade) := by
    rw [_sum_shade_eq_fullness_mul_sum_carrier (E := E) s V h_sum_carrier_s_pos]
    exact mul_le_mul_of_nonneg_right
      (by simpa using NNReal.coe_le_coe.mpr hFull) h_sum_carrier_s_pos.le
  have h_descent : (δ : ℝ) ^ η₀ *
      (∑ i ∈ s', volume.real (V i).carrier) ≤ (∑ i ∈ s', volume.real (V i).shade) :=
    fullness_descent_block (δ := (δ : ℝ)) hδ_pos hM_pos_real hM_abs2_δ
      h_sum_carrier_s_pos h_sE_c_le_s_c h_full_lb h_pig_shade
  have h_descent_T'' : (δ : ℝ) ^ η₀ *
      (∑ i ∈ s', volume.real (V'' i).carrier) ≤ (∑ i ∈ s', volume.real (V'' i).shade) := by
    rw [Finset.sum_congr rfl h_T''_c, Finset.sum_congr rfl h_T''_sh]; exact h_descent
  rw [_sum_shade_eq_fullness_mul_sum_carrier (E := E) s' V'' hsE'_c_pos] at h_descent_T''
  rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_rpow]
  exact le_of_mul_le_mul_right h_descent_T'' hsE'_c_pos

/-- Final multiplicity-absorption chain for the `ball2_version` flow. Given the
`s'`-bound `mul_s' ≤ δ^(-(ε/4) - 2β) * (s'.card * δ^(n-1))^(1-β/2)` and the loss
factors `M ≤ δ^(-(ε/4))`, `s'.card ≤ s.card`, conclude
`M · mul_s' ≤ δ^(-ε - 2β) * (s.card * δ^(n-1))^(1-β/2)`. -/
lemma ball2_mult_absorb_loss
    {ε β : ℝ} (hε_pos : 0 < ε) (hβ_le : β ≤ 2)
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) (hδ_lt_one : δ < 1)
    {M : ℕ} {n : ℕ}
    {s'_card s_card : ℕ} (hs'_le : s'_card ≤ s_card)
    (hM_abs1_δ : (M : ℝ) ≤ (δ : ℝ) ^ (-(ε / 4)))
    {mul_s' : ENNReal}
    (h_mul_s' : mul_s' ≤ (δ : ENNReal) ^ (-(ε / 4) - 2 * β) *
      ((s'_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2)) :
    (M : ENNReal) * mul_s' ≤
      (δ : ENNReal) ^ (-ε - 2 * β) *
        ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
  calc (M : ENNReal) * mul_s'
      ≤ (M : ENNReal) *
          ((δ : ENNReal) ^ (-(ε / 4) - 2 * β) *
            ((s'_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2)) := by gcongr
    _ ≤ (M : ENNReal) *
          ((δ : ENNReal) ^ (-(ε / 4) - 2 * β) *
            ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2)) := by
          have : (s'_card : ENNReal) ≤ s_card := by exact_mod_cast hs'_le
          gcongr; linarith
    _ ≤ (δ : ENNReal) ^ (-(ε / 4)) *
          ((δ : ENNReal) ^ (-(ε / 4) - 2 * β) *
            ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2)) := by
          have hM_enn : (M : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 4)) := by
            rw [ennreal_coe_nnreal_rpow hδ_pos, ← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal hM_abs1_δ
          gcongr
    _ = (δ : ENNReal) ^ (-(ε / 4) + (-(ε / 4) - 2 * β)) *
          ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
          rw [← mul_assoc,
              ← ENNReal.rpow_add _ _ (by exact_mod_cast hδ_pos.ne') ENNReal.coe_ne_top]
    _ ≤ (δ : ENNReal) ^ (-ε - 2 * β) *
          ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
          gcongr ?_ * _
          apply ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_lt_one.le)
          linarith

/-- Bundles the seven eventual events used in `ball2_version`'s
`filter_upwards` block: `M ≤ δ^(-ε/4)`, `M ≤ δ^(η-η₀)`, `M ≤ δ^(2η-η₀)`,
`δ < 1`, `δ < 1/4`, `0 < δ`, conjoined with each other. -/
lemma ball2_event_bundle (M : ℕ) {ε η η₀ : ℝ}
    (hε : 0 < ε / 4) (hη₀_pos : 0 < η₀) (h_eta_lt : η ≤ η₀ / 8) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      (M : ℝ) ≤ (δ : ℝ) ^ (-(ε / 4)) ∧ (M : ℝ) ≤ (δ : ℝ) ^ (η - η₀) ∧
      (M : ℝ) ≤ (δ : ℝ) ^ (2 * η - η₀) ∧ (δ : ℝ) < 1 ∧
      (δ : ℝ) < 1 / 4 ∧ 0 < (δ : ℝ) := by
  filter_upwards [
    nnreal_eventually_of_real_eventually (cast_eventually_le_rpow_neg M (ε / 4) hε),
    nnreal_eventually_of_real_eventually
      ((cast_eventually_le_rpow_neg M (η₀ - η) (by linarith)).mono
        fun _ hδ => by rwa [show η - η₀ = -(η₀ - η) from by ring] :
      ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (M : ℝ) ≤ δ ^ (η - η₀)),
    nnreal_eventually_of_real_eventually
      ((cast_eventually_le_rpow_neg M (η₀ - 2 * η) (by linarith)).mono
        fun _ hδ => by rwa [show 2 * η - η₀ = -(η₀ - 2 * η) from by ring] :
      ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (M : ℝ) ≤ δ ^ (2 * η - η₀)),
    nnreal_eventually_of_real_eventually
      (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one) : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1),
    nnreal_eventually_of_real_eventually
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)) :
      ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1/4),
    nnreal_eventually_of_real_eventually
      (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ)]
    with δ h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Absorbing the Frostman constant `C_big = δ^(-η) · (M · δ^(-η) · V_unit/V_B2)`
into a single `δ^(-η₀)` using `M ≤ δ^(2η - η₀)` and `V_unit ≤ V_B2`. -/
private lemma C_big_le_rpow {δ : ℝ} (hδ_pos : 0 < δ) {M η η₀ V_unit V_B2 : ℝ}
    (hM_nn : 0 ≤ M) (hV_B2_pos : 0 < V_B2)
    (hV_le : V_unit ≤ V_B2)
    (hM_abs3 : M ≤ δ ^ (2 * η - η₀)) :
    δ ^ (-η) * (M * δ ^ (-η) * V_unit / V_B2) ≤ δ ^ (-η₀) :=
  calc δ ^ (-η) * (M * δ ^ (-η) * V_unit / V_B2)
      = M * δ ^ (-(2 * η)) * (V_unit / V_B2) := by
        rw [show δ ^ (-(2 * η)) = δ ^ (-η) * δ ^ (-η) from by
          rw [← Real.rpow_add hδ_pos]; ring_nf]
        field_simp
    _ ≤ M * δ ^ (-(2 * η)) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hV_B2_pos).mpr hV_le)
          (mul_nonneg hM_nn (Real.rpow_nonneg hδ_pos.le _))
    _ ≤ δ ^ (2 * η - η₀) * δ ^ (-(2 * η)) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right hM_abs3 (Real.rpow_nonneg hδ_pos.le _)
    _ = δ ^ (-η₀) := by rw [← Real.rpow_add hδ_pos]; ring_nf

/-- Bookkeeping identity collapsing the product of two `ENNReal.ofReal`s and the
unit/B₂ volume ratio into `ENNReal.ofReal C_big`. -/
lemma C_big_ofReal_eq {δ : ℝ} (hδ_pos : 0 < δ) {η M V_unit V_B2 : ℝ}
    (hM_nn : 0 ≤ M) (hV_B2_pos : 0 < V_B2)
    {U B : ENNReal}
    (hU_eq : U = ENNReal.ofReal V_unit) (hB_eq : B = ENNReal.ofReal V_B2) :
    ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (M * δ ^ (-η)) * (U / B) =
      ENNReal.ofReal (δ ^ (-η) * (M * δ ^ (-η) * V_unit / V_B2)) := by
  have h_factor_nn : 0 ≤ δ ^ (-η) * (M * δ ^ (-η)) :=
    mul_nonneg (Real.rpow_nonneg hδ_pos.le _)
      (mul_nonneg hM_nn (Real.rpow_nonneg hδ_pos.le _))
  rw [hU_eq, hB_eq, ← ENNReal.ofReal_div_of_pos hV_B2_pos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _),
      ← ENNReal.ofReal_mul h_factor_nn]
  congr 1
  ring

/-- Transfer the Frostman estimate to the translated heavy subfamily and absorb its constant. -/
lemma frostman_translate_absorb
    {ι : Type*} {s s' : Finset ι} (hs'_sub : s' ⊆ s)
    (W : ι → ConvexSpaceBody E) {W'' : ι → ConvexSpaceBody E} (v : E) {B U : ConvexSpaceBody E}
    (hT_in_B : ∀ i ∈ s, W i ≤ B)
    (hT''_eqOn : ∀ i ∈ s', W'' i = (W i).translate v)
    (hT''_in_U : ∀ i ∈ s', W'' i ≤ U)
    {δ η η₀ M_real V_unit V_B : ℝ}
    (hδ_pos : 0 < δ) (hM_nn : 0 ≤ M_real) (hV_B_pos : 0 < V_B)
    (hV_le : V_unit ≤ V_B)
    (hM_abs3 : M_real ≤ δ ^ (2 * η - η₀))
    (hU_eq : volume U.carrier = ENNReal.ofReal V_unit)
    (hB_eq : volume B.carrier = ENNReal.ofReal V_B)
    (hU_ne_zero : volume U.carrier ≠ 0) (hB_ne_zero : volume B.carrier ≠ 0)
    (hFrost : IsFrostmanIn s W B (ENNReal.ofReal (δ ^ (-η))))
    (h_carrier_bound : (∑ i ∈ s, volume (W i).carrier) ≤
      ENNReal.ofReal (M_real * δ ^ (-η)) * (∑ i ∈ s', volume (W i).carrier)) :
    IsFrostmanIn s' (fun i => W'' i) U (ENNReal.ofReal (δ ^ (-η₀))) := by
  have hT'_in_U : ∀ i ∈ s', (W i).translate v ≤ U := fun i hi => by
    rw [← hT''_eqOn i hi]
    exact hT''_in_U i hi
  have hFrost_T' : IsFrostmanIn s' (fun i => (W i).translate v) U
      (ENNReal.ofReal (δ ^ (-η) * (M_real * δ ^ (-η) * V_unit / V_B))) := by
    rw [← C_big_ofReal_eq hδ_pos hM_nn hV_B_pos hU_eq hB_eq]
    exact hFrost.translate_of_le_of_subset hT_in_B hs'_sub h_carrier_bound v hT'_in_U
      hB_ne_zero hU_ne_zero
  have hFrost_T'' : IsFrostmanIn s' W'' U
      (ENNReal.ofReal (δ ^ (-η) * (M_real * δ ^ (-η) * V_unit / V_B))) :=
    isFrostmanIn_of_eqOn (E := E) (fun i hi => (hT''_eqOn i hi).symm) hFrost_T'
  exact isFrostmanIn_mono_helper (E := E) hFrost_T''
    (ENNReal.ofReal_le_ofReal (C_big_le_rpow hδ_pos hM_nn hV_B_pos hV_le hM_abs3))

/-- [B₂-version of KF(β)]
    If `KF(β)` holds for tubes in `B₁`, then an analogous estimate holds for
    tubes in `B₂ = closedBall 0 2`, with the Frostman condition measured
    relative to `B₂`. -/
theorem FrostmanEstimate.ball2_version [Nontrivial E] {β : ℝ} (hβ_le : β ≤ 2)
    (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 2) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 ConvexSpaceBody.closedUnitBall)
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        δ ^ (-ε - 2 * β) *
        (s.card * δ ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  classical
  intro ε hε
  obtain ⟨η₀, hη₀_pos, h_apply⟩ := h (ε / 4) (by linarith)
  obtain ⟨xs, hxs_norm, _hxs_cover, hxs_assign⟩ := exists_unit_ball_assignment (E := E)
  set M : ℕ := xs.card
  set η : ℝ := min (η₀ / 8) (ε / 16)
  refine ⟨η, lt_min (by linarith) (by linarith), ?_⟩
  filter_upwards [h_apply,
      ball2_event_bundle M (by linarith : (0 : ℝ) < ε / 4) hη₀_pos
        (min_le_left (η₀/8) (ε/16))]
    with δ h_apply_δ hbundle
  obtain ⟨hM_abs1_δ, hM_abs2_δ, hM_abs3_δ, hδ_lt_one, hδ_lt_quarter, hδ_pos⟩ := hbundle
  intro ι s T hB hED hFrost hFull
  by_cases hs_empty : s = ∅
  · subst hs_empty
    simp [ShadedBody.multiplicity_empty]
  have hs_ne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
  have hxs_ne : xs.Nonempty :=
    let ⟨x, hx, _⟩ := Set.mem_iUnion₂.mp (_hxs_cover (Metric.mem_closedBall_self (by norm_num)))
    ⟨x, hx⟩
  have hM_pos_real : (0 : ℝ) < M := Nat.cast_pos.mpr (Finset.card_pos.mpr hxs_ne)
  set f : ι → E := fun i =>
    if hi : i ∈ s then Classical.choose (hxs_assign hδ_lt_quarter.le (T i).toTube (hB i))
    else hxs_ne.choose
  have hf_mem : ∀ i ∈ s, f i ∈ xs := fun i hi => by
    simp only [f, dif_pos hi]; exact (Classical.choose_spec
      (hxs_assign hδ_lt_quarter.le _ (hB i))).1
  have hf_subset : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (f i) 1 := fun i hi => by
    simp only [f, dif_pos hi]; exact (Classical.choose_spec
      (hxs_assign hδ_lt_quarter.le _ (hB i))).2
  obtain ⟨k₀, hk₀_mem, h_pig_shade⟩ :=
    exists_block_sum_ge s f xs (fun i => volume.real (T i).toShadedBody.shade)
      hxs_ne hf_mem
  set s' : Finset ι := {i ∈ s | f i = k₀}
  have hs'_sub : s' ⊆ s := Finset.filter_subset _ _
  let v : E := -k₀
  let T' : ι → ShadedTube δ E := fun i => (T i).translate v
  have hT'_carrier_s' : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi p hp => by
      obtain ⟨q, hq, rfl⟩ := show p ∈ (v + ·) '' (T i).carrier from hp
      have hq_in := hf_subset i (hs'_sub hi) hq
      rw [Metric.mem_closedBall, dist_eq_norm,
        show v + q - 0 = q - f i from by
          rw [(Finset.mem_filter.mp hi).2]; simp only [v]; abel]
      rwa [Metric.mem_closedBall, dist_eq_norm] at hq_in
  set n : ℕ := Module.finrank ℝ E
  -- ENNReal version of the pigeon-shade inequality (needed by `multiplicity_pigeon_transfer`).
  have hfin : ∀ i, volume (T i).toShadedBody.shade ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (T i).toShadedBody.isCompact'.measure_ne_top
      (measure_mono (T i).toShadedBody.shade_subset)
  have h_pig_shade_enn :
      (∑ i ∈ s, volume (T i).toShadedBody.shade) ≤
        (M : ENNReal) * (∑ i ∈ s', volume (T i).toShadedBody.shade) := by
    rw [sum_volume_ofReal_eq _ s _ (fun i _ => hfin i),
        sum_volume_ofReal_eq _ s' _ (fun i _ => hfin i),
        ← ENNReal.ofReal_natCast (M : ℕ), ← ENNReal.ofReal_mul hM_pos_real.le]
    exact ENNReal.ofReal_le_ofReal h_pig_shade
  by_cases hs'_empty : s' = ∅
  · have hmu_le := multiplicity_pigeon_transfer (E := E) hs'_sub
      (fun i => (T i).toShadedBody) h_pig_shade_enn
    rw [hs'_empty, ShadedBody.multiplicity_empty, mul_zero] at hmu_le
    exact hmu_le.trans bot_le
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hs'_empty
  let T'' : ι → ShadedTube δ E := fun i => if i ∈ s' then T' i else T' i₀
  have hT''_eq_T' : ∀ i ∈ s', T'' i = T' i := fun i hi => by simp only [T'', if_pos hi]
  have hED'' : (s' : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((T'' i).carrier) ((T'' j).carrier)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    rw [hT''_eq_T' i hi, hT''_eq_T' j hj]
    exact (isEssentiallyDistinct_translate (T i).carrier (T j).carrier v).mpr
      (hED (hs'_sub hi) (hs'_sub hj) hij)
  set B2 := ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) with hB2_def
  have hCarrier_B2 : B2.carrier = Metric.closedBall (0 : E) 2 := by
    rw [hB2_def, cthickening_closedUnitBall_carrier (E := E) 1 zero_le_one]; norm_num
  have hV_B2_pos : 0 < volume.real B2.carrier :=
    hCarrier_B2 ▸ volume_real_closedBall_pos (E := E) (by norm_num)
  have hT_in_B2 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ B2 :=
    fun i _ x hx => show x ∈ (_ : ConvexSpaceBody E).carrier from hCarrier_B2 ▸ hB i hx
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hc_vol_pos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) :=
    NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hT_vol_pos : ∀ i ∈ s, 0 < volume.real (T i).toConvexSpaceBody.carrier := fun i _ =>
    lt_of_lt_of_le (mul_pos hc_vol_pos (pow_pos hδ_pos _)) (tube_le_volume_real E (T i))
  have h_carrier_bound :
      (∑ i ∈ s, volume.real (T i).toConvexSpaceBody.carrier) ≤
      (M : ℝ) * (δ : ℝ) ^ (-η) *
        (∑ i ∈ s', volume.real (T i).toConvexSpaceBody.carrier) :=
    carrier_pigeon_bound (E := E) hs_ne (fun i => (T i).toShadedBody) hT_vol_pos
      hδ_pos hM_pos_real hFull h_pig_shade
  set V_B2 := volume.real B2.carrier
  set V_unit := volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier
  have hvol_unit_ne_top : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ ⊤ :=
    (ConvexSpaceBody.closedUnitBall (E := E)).isCompact.measure_ne_top
  have hvol_unit_ne_zero : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 zero_lt_one).ne' ∘
      (ConvexSpaceBody.closedUnitBall_carrier (E := E) ▸ ·)
  have hvol_B2_ne_top : volume B2.carrier ≠ ⊤ := B2.isCompact.measure_ne_top
  have hvol_B2_ne_zero : volume B2.carrier ≠ 0 := by
    rw [hCarrier_B2]; exact (Metric.measure_closedBall_pos volume 0 (by norm_num)).ne'
  -- T'' i = T' i on s', so the carrier volume agrees.
  have hT''_eqOn : ∀ i ∈ s', (T'' i).toConvexSpaceBody =
      (T i).toConvexSpaceBody.translate v := fun i hi => by
    rw [hT''_eq_T' i hi]; rfl
  -- T''_i ≤ closedUnitBall for i ∈ s'.
  have hT''_in_unit : ∀ i ∈ s', (T'' i).toConvexSpaceBody ≤
      ConvexSpaceBody.closedUnitBall (E := E) := fun i hi x hx => by
    rw [hT''_eq_T' i hi] at hx
    change x ∈ (_ : ConvexSpaceBody E).carrier
    exact ConvexSpaceBody.closedUnitBall_carrier (E := E) ▸ hT'_carrier_s' i hi hx
  have hC_ne_top : ∀ i, volume (T i).toConvexSpaceBody.carrier ≠ ⊤ :=
    fun i => (T i).toConvexSpaceBody.isCompact'.measure_ne_top
  -- ENNReal version of the carrier-sum pigeon bound.
  have h_carrier_bound_enn :
      (∑ i ∈ s, volume (T i).toConvexSpaceBody.carrier) ≤
        ENNReal.ofReal ((M : ℝ) * (δ : ℝ) ^ (-η)) *
          (∑ i ∈ s', volume (T i).toConvexSpaceBody.carrier) := by
    have h_factor_nn : (0 : ℝ) ≤ (M : ℝ) * (δ : ℝ) ^ (-η) :=
      mul_nonneg hM_pos_real.le (Real.rpow_nonneg hδ_pos.le _)
    rw [sum_volume_ofReal_eq _ s _ (fun i _ => hC_ne_top i),
        sum_volume_ofReal_eq _ s' _ (fun i _ => hC_ne_top i),
        ← ENNReal.ofReal_mul h_factor_nn]
    exact ENNReal.ofReal_le_ofReal h_carrier_bound
  -- Frostman descent + constant absorption to `δ^(-η₀)` on the translated family.
  have hV_unit_le_V_B2 : V_unit ≤ V_B2 :=
    ENNReal.toReal_mono B2.isCompact.measure_lt_top.ne
      (MeasureTheory.measure_mono fun x hx =>
        show x ∈ (_ : ConvexSpaceBody E).carrier from
        hCarrier_B2 ▸ Metric.closedBall_subset_closedBall (by norm_num) hx)
  have hFrost_T'' :
      IsFrostmanIn s' (fun i => (T'' i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall (E := E))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η₀))) :=
    frostman_translate_absorb (E := E) hs'_sub (fun i => (T i).toConvexSpaceBody) v
      hT_in_B2 hT''_eqOn hT''_in_unit hδ_pos hM_pos_real.le
      hV_B2_pos hV_unit_le_V_B2 hM_abs3_δ
      (ENNReal.ofReal_toReal hvol_unit_ne_top).symm
      (ENNReal.ofReal_toReal hvol_B2_ne_top).symm
      hvol_unit_ne_zero hvol_B2_ne_zero
      hFrost h_carrier_bound_enn
  have h_T''_c : ∀ i ∈ s', volume.real (T'' i).toShadedBody.carrier =
      volume.real (T i).toShadedBody.carrier := fun i hi => by
    rw [hT''_eq_T' i hi]; exact MeasureTheory.measureReal_image_add _ _ _
  have h_T''_sh : ∀ i ∈ s', volume.real (T'' i).toShadedBody.shade =
      volume.real (T i).toShadedBody.shade := fun i hi => by
    rw [hT''_eq_T' i hi]; exact MeasureTheory.measureReal_image_add _ _ _
  have hFull' : ShadedBody.fullness s' (fun i ↦ (T'' i).toShadedBody) ≥ δ ^ η₀ :=
    fullness_translate_descent (E := E) hs'_sub hs_ne
      (Finset.nonempty_iff_ne_empty.mpr hs'_empty)
      (fun i => (T i).toShadedBody) (fun i => (T'' i).toShadedBody)
      h_T''_c h_T''_sh hT_vol_pos hδ_pos hM_pos_real hM_abs2_δ hFull h_pig_shade
  -- Bridge `hFrost_T''` to the `(δ : ENNReal) ^ (-η₀)` form expected by `h_apply_δ`.
  have hFrost_T''_ENN :
      IsFrostmanIn s' (fun i => (T'' i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall (E := E))
        ((δ : ENNReal) ^ (-η₀)) := by
    rw [ennreal_coe_nnreal_rpow hδ_pos]; exact hFrost_T''
  have hB_T'' : ∀ i, (T'' i).carrier ⊆ Metric.closedBall 0 1 := fun i => by
    change (if i ∈ s' then T' i else T' i₀).carrier ⊆ _
    split_ifs with hi <;> [exact hT'_carrier_s' i hi; exact hT'_carrier_s' i₀ hi₀]
  -- Inner ENNReal multiplicity bound on `s'`/`T''`.
  have h_mult_ENN := h_apply_δ s' T'' (fun i _ => hB_T'' i) hED'' hFrost_T''_ENN hFull'
  -- Bridge T'' back to T via translation.
  have h_T''_eq : ∀ i ∈ s', (T'' i).toShadedBody = ((T i).toShadedBody).translate v :=
    fun i hi => by rw [hT''_eq_T' i hi]; rfl
  have h_mult_eq :
      ShadedBody.multiplicity s' (fun i => (T'' i).toShadedBody) =
        ShadedBody.multiplicity s' (fun i => (T i).toShadedBody) := by
    rw [multiplicity_eq_of_eqOn (E := E) s' h_T''_eq]
    exact ShadedBody.multiplicity_translate_const s' _ v
  rw [h_mult_eq] at h_mult_ENN
  exact (multiplicity_pigeon_transfer (E := E) hs'_sub _ h_pig_shade_enn).trans
    (ball2_mult_absorb_loss hε hβ_le hδ_pos hδ_lt_one
      (Finset.card_le_card hs'_sub) hM_abs1_δ h_mult_ENN)

/-- For the EDUpToMult flow, the pigeonhole and fullness inequalities force the
subset carrier mass to be positive. -/
private lemma sE_c_pos_of_pigeon
    {δ : ℝ} (hδ_pos : 0 < δ)
    {M_cap : ℕ} {η s_c sE_c sE_sh s_sh : ℝ}
    (h_sc_pos : 0 < s_c) (h_sE_c_nn : 0 ≤ sE_c)
    (h_sE_sh_nn : 0 ≤ sE_sh) (h_sE_sh_le_c : sE_sh ≤ sE_c)
    (h_full_lb : δ ^ η * s_c ≤ s_sh)
    (h_shade_pig : s_sh ≤ ((M_cap : ℝ) + 1) * sE_sh) :
    0 < sE_c := by
  rcases lt_or_ge (0 : ℝ) sE_c with hpos | h
  · exact hpos
  have hsE_c_zero : sE_c = 0 := le_antisymm h h_sE_c_nn
  have hsE_sh_zero : sE_sh = 0 :=
    le_antisymm (le_trans h_sE_sh_le_c hsE_c_zero.le) h_sE_sh_nn
  have h_s_sh_zero : s_sh ≤ 0 := by
    have := h_shade_pig
    rw [hsE_sh_zero, mul_zero] at this
    exact this
  have h_full_pos : 0 < δ ^ η * s_c :=
    mul_pos (Real.rpow_pos_of_pos hδ_pos _) h_sc_pos
  linarith

/-- Combining shade pigeonholing with fullness controls the original carrier mass
by the carrier mass of the selected subfamily. -/
private lemma s_c_le_pigeon
    {δ : ℝ} (hδ_pos : 0 < δ)
    {M_cap : ℕ} {η s_c sE_c sE_sh s_sh : ℝ}
    (h_sE_sh_le_c : sE_sh ≤ sE_c)
    (h_full_lb : δ ^ η * s_c ≤ s_sh)
    (h_shade_pig : s_sh ≤ ((M_cap : ℝ) + 1) * sE_sh) :
    s_c ≤ ((M_cap : ℝ) + 1) * δ ^ (-η) * sE_c := by
  have hM1_nn : (0 : ℝ) ≤ ((M_cap : ℝ) + 1) := by positivity
  have h_combined : δ ^ η * s_c ≤ ((M_cap : ℝ) + 1) * sE_c := calc
    δ ^ η * s_c ≤ s_sh := h_full_lb
    _ ≤ ((M_cap : ℝ) + 1) * sE_sh := h_shade_pig
    _ ≤ ((M_cap : ℝ) + 1) * sE_c :=
      mul_le_mul_of_nonneg_left h_sE_sh_le_c hM1_nn
  have h_rpow_pos : (0 : ℝ) < δ ^ η := Real.rpow_pos_of_pos hδ_pos _
  rw [show (δ ^ (-η) : ℝ) = (δ ^ η)⁻¹ from Real.rpow_neg hδ_pos.le _,
      mul_right_comm, ← div_eq_mul_inv, le_div_iff₀ h_rpow_pos]
  linarith [h_combined]

/-- Fullness descends through the EDUpToMult pigeonhole after absorbing the
factor `M_cap + 1` into the exponent. -/
private lemma fullness_descent_of_pigeon
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ ≤ 1)
    {M_cap : ℕ} {η η₀ s_c sE_c sE_sh s_sh : ℝ}
    (hMδ : ((M_cap : ℝ) + 1) ≤ δ ^ (-η))
    (h2 : 2 * η ≤ η₀)
    (hsE_c_pos : 0 < sE_c) (h_sE_c_le_s_c : sE_c ≤ s_c)
    (h_full_lb : δ ^ η * s_c ≤ s_sh)
    (h_shade_pig : s_sh ≤ ((M_cap : ℝ) + 1) * sE_sh) :
    δ ^ η₀ * sE_c ≤ sE_sh := by
  have hM1_pos : (0 : ℝ) < ((M_cap : ℝ) + 1) := by positivity
  have h_step1 : ((M_cap : ℝ) + 1) * (δ ^ η₀) ≤ δ ^ η := by
    have h1 : ((M_cap : ℝ) + 1) * (δ ^ η₀) ≤ δ ^ (-η) * δ ^ η₀ :=
      mul_le_mul_of_nonneg_right hMδ (Real.rpow_nonneg hδ_pos.le _)
    have h2' : δ ^ (-η) * δ ^ η₀ ≤ δ ^ η := by
      rw [← Real.rpow_add hδ_pos]
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ1 (by linarith)
    exact h1.trans h2'
  have h_chain :
      ((M_cap : ℝ) + 1) * (δ ^ η₀ * sE_c) ≤ ((M_cap : ℝ) + 1) * sE_sh := by
    have e1 : ((M_cap : ℝ) + 1) * (δ ^ η₀ * sE_c) =
        (((M_cap : ℝ) + 1) * δ ^ η₀) * sE_c := by ring
    have l1 : (((M_cap : ℝ) + 1) * δ ^ η₀) * sE_c ≤ δ ^ η * sE_c :=
      mul_le_mul_of_nonneg_right h_step1 hsE_c_pos.le
    have l2 : δ ^ η * sE_c ≤ δ ^ η * s_c :=
      mul_le_mul_of_nonneg_left h_sE_c_le_s_c (Real.rpow_nonneg hδ_pos.le _)
    linarith
  exact le_of_mul_le_mul_left h_chain hM1_pos

/-- **K_F variant under the relaxed `IsEDUpToMult` hypothesis.**

This is the `essentially distinct up to multiplicity` version of
`FrostmanEstimate.ball2_version`: it replaces the strict
`Pairwise IsEssentiallyDistinct` clause by `IsEDUpToMult s _ M_cap` (where
`M_cap` is a fixed natural). The conclusion is identical.

This is exactly the form produced by [GWZ, Section 9, Lemma `randCF`], where
the random translation / Chernoff bound yields multiplicity `≲ 1` for the
"bad" set rather than strict essential distinctness. -/
theorem FrostmanEstimate.ball2_version_edUpToMult [Nontrivial E] {β : ℝ} (hβ_le : β ≤ 2)
    (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E) (M_cap : ℕ),
      ((M_cap : ℝ) + 1 ≤ (δ : ℝ) ^ (-η)) →
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 2) →
      IsEDUpToMult s (fun i => (T i).carrier) M_cap →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 ConvexSpaceBody.closedUnitBall)
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        δ ^ (-ε - 2 * β) *
        (s.card * δ ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  classical
  intro ε hε
  obtain ⟨η₀, hη₀_pos, h_inner⟩ :=
    FrostmanEstimate.ball2_version (E := E) hβ_le h (ε / 2) (by linarith)
  set η : ℝ := min (η₀ / 3) (ε / 4) with hη_def
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  have hη_third : η ≤ η₀ / 3 := min_le_left _ _
  have hη_eps : η ≤ ε / 4 := min_le_right _ _
  refine ⟨η, hη_pos, ?_⟩
  filter_upwards [h_inner,
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one),
      self_mem_nhdsWithin]
    with δ h_inner_δ hδ_lt_one hδ_pos
  intro ι s T M_cap h_Mδ_real hB hED hFrost hFull
  have hδ_pos : 0 < δ := hδ_pos.out
  by_cases hs_empty : s = ∅
  · subst hs_empty
    simp [ShadedBody.multiplicity_empty]
  -- Shade-weighted ED refinement: pass from `IsEDUpToMult` to strict Pairwise ED.
  obtain ⟨s_ED, hs_ED_sub, hs_ED_pairwise, h_shade_pig⟩ :=
    hED.exists_pairwise_subset_with_weight
      (fun i => volume.real (T i).toShadedBody.shade)
      (fun _ _ => ENNReal.toReal_nonneg)
  -- Tube volume positivity on `s` (from the `ShadedTube` lower bound).
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hc_vol : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  have hT_vol_pos : ∀ i ∈ s, 0 < volume.real (T i).toConvexSpaceBody.carrier := fun i _ =>
    lt_of_lt_of_le (mul_pos hc_vol_pos (pow_pos hδ_pos _)) (hc_vol δ hδ_pos (T i).toTube)
  -- Carrier sums.
  set s_c : ℝ := ∑ i ∈ s, volume.real (T i).toShadedBody.carrier with hs_c_def
  set s_sh : ℝ := ∑ i ∈ s, volume.real (T i).toShadedBody.shade with hs_sh_def
  set sE_c : ℝ := ∑ i ∈ s_ED, volume.real (T i).toShadedBody.carrier with hsE_c_def
  set sE_sh : ℝ := ∑ i ∈ s_ED, volume.real (T i).toShadedBody.shade with hsE_sh_def
  have h_sc_pos : 0 < s_c :=
    Finset.sum_pos (fun i hi => hT_vol_pos i hi) (Finset.nonempty_iff_ne_empty.mpr hs_empty)
  have h_sE_sh_le_c : sE_sh ≤ sE_c := Finset.sum_le_sum fun i _ =>
    ENNReal.toReal_mono (T i).toShadedBody.isCompact'.measure_lt_top.ne
      (MeasureTheory.measure_mono (T i).toShadedBody.shade_subset)
  have h_sE_c_le_s_c : sE_c ≤ s_c :=
    Finset.sum_le_sum_of_subset_of_nonneg hs_ED_sub (fun _ _ _ => ENNReal.toReal_nonneg)
  have h_full_lb : (δ : ℝ) ^ η * s_c ≤ s_sh := by
    rw [hs_c_def, hs_sh_def,
      _sum_shade_eq_fullness_mul_sum_carrier (E := E) s
        (fun i => (T i).toShadedBody) h_sc_pos]
    exact mul_le_mul_of_nonneg_right
      (by simpa [NNReal.coe_rpow] using NNReal.coe_le_coe.mpr hFull) h_sc_pos.le
  have hM1_pos_real : (0 : ℝ) < ((M_cap : ℝ) + 1) := by positivity
  have hM1_nn : (0 : ℝ) ≤ ((M_cap : ℝ) + 1) := hM1_pos_real.le
  -- `sE_c > 0`: otherwise `s_sh ≤ (M+1) · sE_sh ≤ (M+1) · sE_c = 0`,
  -- contradicting `δ^η · s_c > 0`.
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hsE_c_pos : 0 < sE_c :=
    sE_c_pos_of_pigeon hδ_pos_real h_sc_pos
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      h_sE_sh_le_c h_full_lb h_shade_pig
  -- Carrier pigeon: `s_c ≤ (M+1) · δ^(-η) · sE_c` (combining shade pigeon with fullness on `s`).
  have h_carrier_bound : s_c ≤ ((M_cap : ℝ) + 1) * δ ^ (-η) * sE_c :=
    s_c_le_pigeon hδ_pos_real h_sE_sh_le_c h_full_lb h_shade_pig
  -- Set `B2 := cthickening 1 closedUnitBall` and its carrier.
  set B2 := ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) with hB2_def
  have hCarrier_B2 : B2.carrier = Metric.closedBall (0 : E) 2 := by
    rw [hB2_def, cthickening_closedUnitBall_carrier (E := E) 1 zero_le_one]; norm_num
  have hT_in_B2 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ B2 :=
    fun i _ x hx => show x ∈ (_ : ConvexSpaceBody E).carrier from hCarrier_B2 ▸ hB i hx
  -- Frostman descent: `IsFrostmanIn s_ED W B2 (δ^(-η) · ((M+1) · δ^(-η)))`.
  have hδ_lt_one_real : ((δ : ℝ) < 1) := by
    have : δ ∈ Set.Iio (1 : NNReal) := hδ_lt_one
    exact_mod_cast this
  have hC_ne_top : ∀ i, volume (T i).toConvexSpaceBody.carrier ≠ ⊤ :=
    fun i => (T i).toConvexSpaceBody.isCompact'.measure_ne_top
  have h_carrier_bound_real : (∑ i ∈ s, volume (T i).toConvexSpaceBody.carrier) ≤
      ENNReal.ofReal (((M_cap : ℝ) + 1) * (δ : ℝ) ^ (-η)) *
        ∑ i ∈ s_ED, volume (T i).toConvexSpaceBody.carrier := by
    have h_factor_nn : (0 : ℝ) ≤ ((M_cap : ℝ) + 1) * (δ : ℝ) ^ (-η) := by positivity
    rw [sum_volume_ofReal_eq _ s _ (fun i _ => hC_ne_top i),
        sum_volume_ofReal_eq _ s_ED _ (fun i _ => hC_ne_top i),
        ← ENNReal.ofReal_mul h_factor_nn]
    exact ENNReal.ofReal_le_ofReal h_carrier_bound
  have hFrost_sED_raw :
      IsFrostmanIn s_ED (fun i => (T i).toConvexSpaceBody) B2
        (ENNReal.ofReal ((δ : ℝ) ^ (-η)) *
          ENNReal.ofReal (((M_cap : ℝ) + 1) * (δ : ℝ) ^ (-η))) :=
    hFrost.of_le_of_subset hT_in_B2 hs_ED_sub h_carrier_bound_real
  -- Absorb the loss factor: `(M+1) · δ^(-η) · δ^(-η) ≤ δ^(-η₀)` since `3η ≤ η₀`.
  have h_const_le : ENNReal.ofReal ((δ : ℝ) ^ (-η)) *
      ENNReal.ofReal (((M_cap : ℝ) + 1) * (δ : ℝ) ^ (-η)) ≤
        ENNReal.ofReal ((δ : ℝ) ^ (-η₀)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos_real.le _)]
    exact ENNReal.ofReal_le_ofReal
      (absorb_M_three_eta_rpow_neg hδ_pos_real hδ_lt_one_real.le h_Mδ_real (by linarith))
  have hFrost_sED : IsFrostmanIn s_ED (fun i => (T i).toConvexSpaceBody) B2
      (ENNReal.ofReal ((δ : ℝ) ^ (-η₀))) := fun K' hK' =>
    (hFrost_sED_raw K' hK').trans
      (mul_le_mul_of_nonneg_right h_const_le bot_le)
  -- Fullness descent: `fullness s_ED ≥ δ^η / (M+1) ≥ δ^(2η) ≥ δ^η₀`.
  have hFull_sED : ShadedBody.fullness s_ED (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₀ := by
    have h_div : (δ : ℝ) ^ η₀ * sE_c ≤ sE_sh :=
      fullness_descent_of_pigeon hδ_pos_real hδ_lt_one_real.le h_Mδ_real
        (by linarith) hsE_c_pos h_sE_c_le_s_c h_full_lb h_shade_pig
    have h_sum_shade :
        sE_sh = (ShadedBody.fullness s_ED (fun i => (T i).toShadedBody) : ℝ) * sE_c := by
      rw [hsE_sh_def, hsE_c_def]
      exact _sum_shade_eq_fullness_mul_sum_carrier (E := E) s_ED
        (fun i => (T i).toShadedBody) hsE_c_pos
    rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_rpow]
    refine le_of_mul_le_mul_right (?_ : (δ : ℝ) ^ η₀ * sE_c ≤ _ * sE_c) hsE_c_pos
    rw [← h_sum_shade]; exact h_div
  -- Apply the strict-ED `ball2_version` on `s_ED` (ENNReal-valued).
  have h_mult_sED : ShadedBody.multiplicity s_ED (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
      ((s_ED.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
    h_inner_δ s_ED T hB hs_ED_pairwise hFrost_sED hFull_sED
  -- ENNReal version of the pigeon-shade inequality.
  have hfin : ∀ i, volume (T i).toShadedBody.shade ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (T i).toShadedBody.isCompact'.measure_ne_top
      (measure_mono (T i).toShadedBody.shade_subset)
  have h_shade_pig_enn :
      (∑ i ∈ s, volume (T i).toShadedBody.shade) ≤
        ((M_cap : ENNReal) + 1) * (∑ i ∈ s_ED, volume (T i).toShadedBody.shade) := by
    rw [enn_natAdd_one_eq_ofReal,
        sum_volume_ofReal_eq _ s _ (fun i _ => hfin i),
        sum_volume_ofReal_eq _ s_ED _ (fun i _ => hfin i),
        ← ENNReal.ofReal_mul hM1_nn]
    exact ENNReal.ofReal_le_ofReal h_shade_pig
  -- Lift to `s` via the multiplicity pigeon transfer (shade preservation).
  have h_pig : ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      ((M_cap : ENNReal) + 1) *
        ShadedBody.multiplicity s_ED (fun i ↦ (T i).toShadedBody) :=
    multiplicity_pigeon_transfer (E := E) hs_ED_sub
      (fun i => (T i).toShadedBody) h_shade_pig_enn
  -- The loss factor `(M+1) ≤ δ^(-η)` in ENNReal.
  have h_Mδ_enn : ((M_cap : ENNReal) + 1) ≤ (δ : ENNReal) ^ (-η) := by
    rw [ennreal_coe_nnreal_rpow hδ_pos_real, enn_natAdd_one_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal h_Mδ_real
  -- Combine and absorb the leftover `(M+1)` factor.
  set n_dim : ℕ := Module.finrank ℝ E
  calc ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
      ≤ ((M_cap : ENNReal) + 1) *
          ShadedBody.multiplicity s_ED (fun i ↦ (T i).toShadedBody) := h_pig
    _ ≤ ((M_cap : ENNReal) + 1) *
        ((δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
          ((s_ED.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) ^ (1 - β / 2)) := by
        gcongr
    _ ≤ ((M_cap : ENNReal) + 1) *
        ((δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) ^ (1 - β / 2)) := by
        gcongr
        linarith
    _ ≤ (δ : ENNReal) ^ (-η) *
        ((δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) ^ (1 - β / 2)) := by
        gcongr
    _ = (δ : ENNReal) ^ (-η + (-(ε / 2) - 2 * β)) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) ^ (1 - β / 2) := by
        rw [← mul_assoc,
            ← ENNReal.rpow_add _ _ (by exact_mod_cast hδ_pos.ne') ENNReal.coe_ne_top]
    _ ≤ (δ : ENNReal) ^ (-ε - 2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) ^ (1 - β / 2) := by
        gcongr ?_ * _
        apply ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_lt_one.le)
        linarith

/-!
### Generalizing `KF(β)` to arbitrary `τ ≤ δ` (Remark 3.6 for `KF`)

The paper's Remark 3.6 states that `KF(β)` implies a version where the Frostman
and fullness parameters use `τ ≤ δ` in place of `δ`. However, unlike the `KKT`
case, the `KF` generalization implicitly requires a polynomial upper bound on
`s.card`. Without such a bound the statement is false: one can duplicate a tube
set arbitrarily many times, inflating `s.card` (and hence the RHS factor
`(s.card * δ^(n-1))^(1-β/2)`) while `µ` stays the same, so the trivial regime
`τ ≪ δ` cannot be handled.

We therefore split the proof into two independent parts, matched by a universal
constant `C > 0`:

  **Part 1 (`generalize_large_tau`):** When `δ^C ≤ τ ≤ δ`, the conditions
  `τ^(-η) ≤ δ^(-η₁)` and `δ^η₁ ≤ τ^η` allow the Frostman and fullness
  hypotheses to be transferred directly to the base `FrostmanEstimate`, and
  then `δ^(-ε) ≤ τ^(-ε)` upgrades the conclusion. No bound on `s.card` is
  needed. The constant `C` is taken as a parameter, and `η = η₁ / C`.

  **Part 2 (`generalize_small_tau`):** When `τ < δ^C`, the factor `τ^(-ε)` is
  at least `δ^(-Cε)`, which is large enough that the trivial bound `µ ≤ |s|`
  already implies the desired estimate — provided `s.card ≤ D * δ^(-A)` for
  some constants `D, A > 0`. The constant `D` is absorbed into a power of `δ`
  for sufficiently small `δ`. This part produces the value of `C` (depending
  on `A, ε, β, n` but not on `D`), and requires neither `FrostmanEstimate` nor
  any Frostman/fullness hypotheses.

The two parts compose as follows: an external cardinality bound (e.g. from
`card_le_of_maxDensity_le`) supplies `A` and `D`; Part 2 determines `C`;
Part 1 then uses that `C` to find `η`. The case split on `τ` is performed
by the caller.
-/

/-- Bridge the ENNReal RHS of the base `FrostmanEstimate` conclusion to the
corresponding expression with `τ`, using `τ ≤ δ` to absorb
`δ^(-ε) ≤ τ^(-ε)`. -/
lemma generalize_large_tau_rhs_le
    {δ : NNReal} (hδ_pos : 0 < δ)
    {τ : NNReal} {ε β : ℝ} (hτ_pos : 0 < τ) (hτ_le : τ ≤ δ) (hε : 0 < ε)
    (n : ℕ) {s_card : ℕ} (hs_pos : 0 < (s_card : ℝ)) :
    (δ : ENNReal) ^ (-ε - 2 * β) *
      ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) ≤
      (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) *
        ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
  have hδ_pos_real : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hτ_pos_real : 0 < (τ : ℝ) := by exact_mod_cast hτ_pos
  have h_δpow_eq : (δ : ENNReal) ^ (n - 1) =
      ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) := by
    rw [ENNReal.ofReal_pow hδ_pos_real.le, ENNReal.ofReal_coe_nnreal]
  have h_card_mul_eq :
      ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) =
      ENNReal.ofReal ((s_card : ℝ) * (δ : ℝ) ^ (n - 1)) := by
    rw [show (s_card : ENNReal) = ENNReal.ofReal (s_card : ℝ) from
          (ENNReal.ofReal_natCast _).symm, h_δpow_eq,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have h_card_mul_pos : (0 : ℝ) < (s_card : ℝ) * (δ : ℝ) ^ (n - 1) :=
    mul_pos hs_pos (pow_pos hδ_pos_real _)
  rw [ennreal_coe_nnreal_rpow hδ_pos_real, ennreal_coe_nnreal_rpow hτ_pos_real, h_card_mul_eq,
      ENNReal.ofReal_rpow_of_pos h_card_mul_pos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos_real.le _),
      ennreal_coe_nnreal_rpow hδ_pos_real,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hτ_pos_real.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hτ_pos_real.le _)
        (Real.rpow_nonneg hδ_pos_real.le _))]
  apply ENNReal.ofReal_le_ofReal
  rw [show -ε - 2 * β = -ε + (-2 * β) from by ring, Real.rpow_add hδ_pos_real,
      mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · rw [Real.rpow_neg hδ_pos_real.le, Real.rpow_neg hτ_pos_real.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hτ_pos_real _)
      (Real.rpow_le_rpow hτ_pos_real.le (by exact_mod_cast hτ_le) hε.le)
  · exact mul_nonneg (Real.rpow_nonneg hδ_pos_real.le _)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg hδ_pos_real.le _)) _)

/-- The `(s.card · δ^(n-1))^(1-β/2)` factor splits as
`(s.card)^(1-β/2) · δ^((n-1)(1-β/2))`. -/
lemma small_tau_rpow_split {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (s_card : ℕ) (β : ℝ) :
    ((s_card : ℝ) * δ ^ (n - 1)) ^ (1 - β / 2) =
      (s_card : ℝ) ^ (1 - β / 2) * δ ^ (((n : ℝ) - 1) * (1 - β / 2)) := by
  rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hδ.le _),
      ← Real.rpow_natCast δ (n - 1), ← Real.rpow_mul hδ.le,
      show (↑(n - 1) : ℝ) = (n : ℝ) - 1 from Nat.cast_pred hn]

/-- The small-`τ` real-valued bound: when `τ < δ^C`, `s.card ≤ D · δ^(-A)`, and
the exponent identity `-L + -(A · β/2) = -(C · ε) + (-2β + (n-1)(1-β/2))` holds,
together with the absorption `D^(β/2) ≤ δ^(-L)`, the trivial bound `s.card`
controls `τ^(-ε) · δ^(-2β) · (s.card · δ^(n-1))^(1-β/2)`. -/
lemma small_tau_real_bound
    {δ τ ε β A D L C : ℝ} {n : ℕ} {s_card : ℕ}
    (hδ_pos : 0 < δ) (hτ_pos : 0 < τ) (hτ_lt : τ < δ ^ C)
    (hε : 0 < ε) (hβ : 0 ≤ β) (hD : 0 < D)
    (hn : 0 < n) (hs_pos : 0 < (s_card : ℝ))
    (hs_card : (s_card : ℝ) ≤ D * δ ^ (-A))
    (h_DL : D ^ (β / 2) ≤ δ ^ (-L))
    (h_exp : -L + -(A * (β / 2)) =
      -(C * ε) + (-2 * β + ((n : ℝ) - 1) * (1 - β / 2))) :
    (s_card : ℝ) ≤
      τ ^ (-ε) * δ ^ (-2 * β) *
        ((s_card : ℝ) * δ ^ (n - 1)) ^ (1 - β / 2) := by
  calc (s_card : ℝ)
      = (s_card : ℝ) ^ (β / 2) * (s_card : ℝ) ^ (1 - β / 2) := by
        rw [← Real.rpow_add hs_pos, show β / 2 + (1 - β / 2) = 1 from by ring,
            Real.rpow_one]
    _ ≤ (τ ^ (-ε) * δ ^ (-2 * β + ((n : ℝ) - 1) * (1 - β / 2))) *
          (s_card : ℝ) ^ (1 - β / 2) := mul_le_mul_of_nonneg_right
          (calc (s_card : ℝ) ^ (β / 2) ≤ (D * δ ^ (-A)) ^ (β / 2) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hs_card (by positivity)
          _ = D ^ (β / 2) * δ ^ (-(A * (β / 2))) := by
              rw [Real.mul_rpow hD.le (Real.rpow_nonneg hδ_pos.le _),
                  ← Real.rpow_mul hδ_pos.le]; congr 1; ring_nf
          _ ≤ δ ^ (-L) * δ ^ (-(A * (β / 2))) :=
              mul_le_mul_of_nonneg_right h_DL (Real.rpow_nonneg hδ_pos.le _)
          _ = δ ^ (-(C * ε)) * δ ^ (-2 * β + ((n : ℝ) - 1) * (1 - β / 2)) := by
              rw [← Real.rpow_add hδ_pos, h_exp, Real.rpow_add hδ_pos]
          _ ≤ τ ^ (-ε) * δ ^ (-2 * β + ((n : ℝ) - 1) * (1 - β / 2)) :=
              mul_le_mul_of_nonneg_right (by
                rw [Real.rpow_neg hδ_pos.le, Real.rpow_neg hτ_pos.le]
                exact inv_anti₀ (Real.rpow_pos_of_pos hτ_pos _) (calc
                  τ ^ ε ≤ (δ ^ C) ^ ε := Real.rpow_le_rpow hτ_pos.le hτ_lt.le hε.le
                  _ = δ ^ (C * ε) := by rw [← Real.rpow_mul hδ_pos.le]))
                (Real.rpow_nonneg hδ_pos.le _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = τ ^ (-ε) * δ ^ (-2 * β) *
          ((s_card : ℝ) * δ ^ (n - 1)) ^ (1 - β / 2) := by
        rw [small_tau_rpow_split hδ_pos hn s_card β, Real.rpow_add hδ_pos]; ring

theorem FrostmanEstimate.generalize_large_tau {β : ℝ} (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∀ C > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ → δ ^ C ≤ τ →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ((τ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^
            (1 - β / 2) := by
  intro ε hε C hC
  obtain ⟨η₁, hη₁_pos, h_base⟩ := h ε hε
  refine ⟨η₁ / C, by positivity, ?_⟩
  filter_upwards [h_base, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one),
    self_mem_nhdsWithin] with δ hδ_base hδ_lt_one hδ_pos
  intro τ hτ_pos hτ_le hτ_ge ι s T hB hED hFrost hFull
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := hδ_pos.out
  have hτ_pos_real : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ_pos
  have h_base_le : (δ : ℝ) ^ η₁ ≤ (τ : ℝ) ^ (η₁ / C) := calc
    (δ : ℝ) ^ η₁ = ((δ : ℝ) ^ C) ^ (η₁ / C) := by
      rw [← Real.rpow_mul hδ_pos_real.le]; congr 1; field_simp
    _ ≤ (τ : ℝ) ^ (η₁ / C) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hδ_pos_real.le _)
        (by exact_mod_cast hτ_ge) (by positivity)
  have hFrost' : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ((δ : ENNReal) ^ (-η₁)) := by
    rw [ennreal_coe_nnreal_rpow hδ_pos_real]
    rw [ennreal_coe_nnreal_rpow hτ_pos_real] at hFrost
    intro K' hK'
    refine (hFrost K' hK').trans (mul_le_mul_of_nonneg_right ?_ bot_le)
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hτ_pos_real.le, Real.rpow_neg hδ_pos_real.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hδ_pos_real _) h_base_le
  have hFull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₁ :=
    le_trans (by exact_mod_cast h_base_le) hFull
  by_cases hs_empty : s = ∅
  · subst hs_empty
    simp [ShadedBody.multiplicity_empty]
  have h_mult_ENN := hδ_base s T (fun i hi => hB i) hED hFrost' hFull'
  have hs_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs_empty)
  exact h_mult_ENN.trans
    (generalize_large_tau_rhs_le hδ_pos hτ_pos hτ_le hε _ hs_pos)

theorem FrostmanEstimate.generalize_small_tau [Nontrivial E] {β : ℝ} (hβ : 0 ≤ β) :
    ∀ ε > (0 : ℝ), ∀ A > (0 : ℝ), ∀ D > (0 : ℝ), ∃ C > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ → τ < δ ^ C →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (s.card : ℝ) ≤ D * (δ : ℝ) ^ (-A) →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^
            (1 - β / 2) := by
  intro ε hε A hA D hD
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set n : ℝ := ↑(Module.finrank ℝ E)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set C := (A + n + 1) * (β + 1) / ε with hC_def
  refine ⟨C, by positivity, ?_⟩
  have hCε : C * ε = (A + n + 1) * (β + 1) := by simp only [hC_def]; field_simp
  set L := C * ε + 2 * β - (n - 1) * (1 - β / 2) - A * β / 2 with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def, hCε]
    nlinarith [mul_nonneg hA.le hβ, mul_nonneg hn_pos.le hβ]
  have h_exp : -L + -(A * (β / 2)) = -(C * ε) + (-2 * β + (n - 1) * (1 - β / 2)) := by
    rw [hL_def]; ring
  filter_upwards [nnreal_eventually_of_real_eventually
      (absorb_const_le_rpow_neg (Real.rpow_pos_of_pos hD (β / 2)) hL_pos),
    nnreal_eventually_of_real_eventually
      (self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ)]
    with δ h_DL hδ_pos
  intro τ hτ_pos hτ_le hτ_lt ι s T hs_card
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := hδ_pos
  have hτ_pos_real : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ_pos
  by_cases hs : s = ∅
  · subst hs; simp [ShadedBody.multiplicity_empty]
  · have hs_pos : (0 : ℝ) < s.card :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs))
    refine (ShadedBody.multiplicity_le_card s _).trans ?_
    rw [show ((s.card : ENNReal)) = ENNReal.ofReal (s.card : ℝ) from
          (ENNReal.ofReal_natCast _).symm,
        ennreal_coe_nnreal_rpow hτ_pos_real, ennreal_coe_nnreal_rpow hδ_pos]
    rw [show (δ : ENNReal) ^ (Module.finrank ℝ E - 1) =
        ENNReal.ofReal ((δ : ℝ) ^ (Module.finrank ℝ E - 1)) by
      rw [ENNReal.ofReal_pow hδ_pos.le, ENNReal.ofReal_coe_nnreal]]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg s.card)]
    rw [ENNReal.ofReal_rpow_of_pos (mul_pos hs_pos (pow_pos hδ_pos _)),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hτ_pos_real.le _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hτ_pos_real.le _)
        (Real.rpow_nonneg hδ_pos.le _))]
    exact ENNReal.ofReal_le_ofReal
      (small_tau_real_bound hδ_pos hτ_pos_real (by exact_mod_cast hτ_lt) hε hβ hD hn
        hs_pos hs_card h_DL h_exp)

theorem FrostmanEstimate.generalize_tau [Nontrivial E] {β : ℝ} (hβ : 0 ≤ β)
    (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ((τ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^
            (1 - β / 2) := by
  intro ε hε
  set D : ℝ := Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)
  have hD_pos : 0 < D := Tube.card_le_of_EssDistinct.C_pos
  obtain ⟨C, hC_pos, hC_ev⟩ := FrostmanEstimate.generalize_small_tau E hβ ε hε
    (2 * (Module.finrank ℝ E)) (by
      have : 0 < Module.finrank ℝ E := Module.finrank_pos
      positivity) D hD_pos
  obtain ⟨η, hη_pos, hη_ev⟩ := h.generalize_large_tau E ε hε C hC_pos
  refine ⟨η, hη_pos, ?_⟩
  filter_upwards [hη_ev, hC_ev, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)]
    with δ hδ_large hδ_small (hδ_pos : 0 < δ) hδ_lt_one
  intro τ hτ_pos hτ_le ι s T hB hED hFrost hFull
  by_cases hcase : δ ^ C ≤ τ
  · exact hδ_large τ hτ_pos hτ_le hcase s T hB hED hFrost hFull
  · push Not at hcase
    apply hδ_small τ hτ_pos hτ_le hcase s T
    calc (s.card : ℝ)
        ≤ D * (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) :=
          Tube.card_le_of_EssDistinct hδ_pos 1 s
          (fun i => (T i).toTube) (fun i _ => hB i) hED
      _ = D * (δ : ℝ) ^ (-((2 : ℝ) * (Module.finrank ℝ E))) := by
          have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := hδ_pos
          congr 1; rw [one_div, inv_pow]
          rw [show (2 : ℝ) * ↑(Module.finrank ℝ E) = ↑(2 * Module.finrank ℝ E) from by
            push_cast; ring]
          rw [Real.rpow_neg hδ_pos_real.le, Real.rpow_natCast]

/-- **[GWZ, Lemma 3.9], canonical form.** If `KF(β)` holds, then for any pairwise essentially
distinct family of `δ`-tubes in `B₁` with fullness at least `δ^η`, the multiplicity is controlled in
terms of the family's own **canonical** Frostman constant.

The eventual `δ`-set is chosen before the family and depends only on `ε`, `β` and the ambient
dimension — in particular not on `s`, on `T`, or on their Frostman constant. This is what the
rigid-motion random-copy theorem `Kakeya.exists_randCF_rigid_family` buys: its `δ`-threshold and its
ED multiplicity cap `M_cap` are both free of `C_F`, replacing the old translation-only
`M_ED := ⌈C_F⌉₊ · C_pack_ext + 1`. -/
theorem FrostmanEstimate.multiplicity_bound {β : ℝ} (_hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
          (ConvexSpaceBody.frostmanConstant s (fun i ↦ (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) *
        (δ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  classical
  have hn_pos : 0 < Module.finrank ℝ E := by linarith
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  obtain ⟨η_mult, hη_mult_pos, hKF_B2_mult⟩ :=
    FrostmanEstimate.ball2_version_edUpToMult (E := E) (by linarith) h (ε / 2)
      (by linarith)
  set c := min (η_mult / 2) (ε / 8) with hc_def
  have hc_pos : 0 < c := lt_min (by linarith) (by linarith)
  have hc_le_eta_mult_half : c ≤ η_mult / 2 := min_le_left _ _
  refine ⟨c, hc_pos, ?_⟩
  have hRandCF := Kakeya.exists_randCF_rigid_family (E := E) hn hη_mult_pos
  have hslack_event := nnreal_eventually_of_real_eventually
    ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -(ε / 2) < 0)).eventually_ge_atTop
      ((2 : ℝ) ^ ((1 : ℝ) - β / 2)))
  filter_upwards [hKF_B2_mult, hRandCF, hslack_event,
    nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)),
    nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ) self_mem_nhdsWithin]
    with δ hδ_KF_B2_mult hδ_randCF hδ_slack hδ_lt_one hδ_pos
  intro ι s T hB hED hfull
  rcases eq_or_ne s ∅ with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  · have hδ_pos' : (0 : ℝ) < (δ : ℝ) := hδ_pos
    have hfull_real : ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)) : ℝ)
        ≥ (δ : ℝ) ^ c := by
      simpa [NNReal.coe_rpow] using NNReal.coe_le_coe.mpr hfull
    have hfull_mult :
        ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)) : ℝ) ≥ (δ : ℝ) ^ η_mult :=
      le_trans (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
        (by linarith [hc_le_eta_mult_half])) hfull_real
    set CFactual : ENNReal := ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall with hCFactual
    have hs_ne : s.Nonempty := Finset.nonempty_of_ne_empty hs
    have hCF_ne_top : CFactual ≠ ⊤ :=
      Tube.frostmanConstant_ne_top hδ_pos s (fun i => (T i).toTube) (fun i _ => hB i)
    have hCF1 : (1 : ENNReal) ≤ CFactual :=
      one_le_frostmanConstant_of_tubes (E := E) (δ := δ) (ι := ι) hδ_pos s T hs_ne
        (fun i _ => hB i)
    obtain ⟨J, ω, M_cap, hJdef, hJpos, hω, hM_cap_bd, hcard_eq, hB2mem, hEDmult, hFrostOut,
        hfullEq, hmu_le⟩ :=
      hδ_randCF s T (fun i _ => hB i) hED (Finset.card_pos.mpr hs_ne)
    let s' : Finset (ι × Fin J) := s ×ˢ (Finset.univ : Finset (Fin J))
    let T' : ι × Fin J → ShadedTube δ E := fun p => rigidProduct T J ω p
    -- `∀ p` (all pairs, not just `p ∈ s'`) B₂ containment, from `hB p.1` and `hω`:
    have hB2 : ∀ p, (T' p).carrier ⊆ Metric.closedBall (0 : E) 2 := by
      intro p
      change (rigidProduct T J ω p).carrier ⊆ Metric.closedBall (0 : E) 2
      rw [rigidProduct_apply]
      rw [ShadedTube.rigidMove_carrier]
      calc
        Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' (T p.1).carrier
            ⊆ Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' Metric.closedBall (0 : E) 1 := by
              exact Set.image_mono (hB p.1)
        _ = Metric.closedBall (Kakeya.rigidMap (ω p.2).1 (ω p.2).2 (0 : E)) (1 : ℝ) :=
              Kakeya.rigidMap_image_closedBall (ω p.2).1 (ω p.2).2 (0 : E) (1 : ℝ)
        _ = Metric.closedBall ((ω p.2).2 : E) (1 : ℝ) := by simp
        _ ⊆ Metric.closedBall (0 : E) (2 : ℝ) := by
              intro x hx
              rw [Metric.mem_closedBall] at hx ⊢
              have hv : dist (ω p.2).2 (0 : E) ≤ (1 : ℝ) := by
                simpa [Metric.mem_closedBall] using hω p.2
              calc
                dist x (0 : E) ≤ dist x (ω p.2).2 + dist (ω p.2).2 (0 : E) :=
                  dist_triangle x (ω p.2).2 (0 : E)
                _ ≤ (1 : ℝ) + (1 : ℝ) := by exact add_le_add hx hv
                _ = (2 : ℝ) := by norm_num
    have hfull_mult_nn : ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η_mult := by
      exact NNReal.coe_le_coe.mp (by simpa [NNReal.coe_rpow] using hfull_mult)
    have hfull_T' : ShadedBody.fullness s' (fun p => (T' p).toShadedBody) ≥ δ ^ η_mult := by
      rw [hfullEq]
      exact hfull_mult_nn
    have hmu_inner :=
      hδ_KF_B2_mult s' T' M_cap hM_cap_bd hB2 hEDmult hFrostOut hfull_T'
    have h_CF_nn : 0 ≤ CFactual.toReal := ENNReal.toReal_nonneg
    have hβ2_nn : 0 ≤ (1 : ℝ) - β / 2 := by linarith
    have hδpow_nn : 0 ≤ (δ : ℝ) ^ (Module.finrank ℝ E - 1) := pow_nonneg hδ_pos'.le _
    have h_inner_nn : 0 ≤ ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by positivity
    have h_inner'_nn : 0 ≤ ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by positivity
    have hJ_le : (J : ℝ) ≤ 2 * CFactual.toReal := by
      rw [hJdef]
      calc
        (⌈CFactual.toReal⌉₊ : ℝ) ≤ CFactual.toReal + 1 :=
          (Nat.ceil_lt_add_one ENNReal.toReal_nonneg).le
        _ ≤ 2 * CFactual.toReal := by
          have : (1 : ℝ) ≤ CFactual.toReal := by
            simpa using ENNReal.toReal_mono hCF_ne_top hCF1
          linarith
    have hcard_chain :
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ≤
          ((2 : ℝ) * CFactual.toReal) * ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
      have h1 : (s'.card : ℝ) ≤ 2 * CFactual.toReal * (s.card : ℝ) := by
        calc
          (s'.card : ℝ) = (J : ℝ) * (s.card : ℝ) := by
            rw [hcard_eq]
            norm_num
          _ ≤ (2 * CFactual.toReal) * (s.card : ℝ) :=
            mul_le_mul_of_nonneg_right hJ_le (Nat.cast_nonneg _)
      have := mul_le_mul_of_nonneg_right h1 hδpow_nn
      linarith [this]
    have hcard_chain_pow :
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) ≤
          ((2 : ℝ) ^ (1 - β / 2) * CFactual.toReal ^ (1 - β / 2)) *
            ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      have h_pow_le := Real.rpow_le_rpow h_inner'_nn hcard_chain hβ2_nn
      rwa [Real.mul_rpow (by positivity) h_inner_nn,
        Real.mul_rpow (by norm_num) h_CF_nn] at h_pow_le
    have hδ_neg_eps_2_nn : 0 ≤ (δ : ℝ) ^ (-(ε / 2) - 2 * β) := Real.rpow_nonneg hδ_pos'.le _
    have hprod_nn : 0 ≤ CFactual.toReal ^ (1 - β / 2) *
        ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by positivity
    set Y : ℝ := (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) with hY_def
    set Z : ℝ := (δ : ℝ) ^ (-ε) * CFactual.toReal ^ (1 - β / 2) * (δ : ℝ) ^ (-2 * β) *
        ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) with hZ_def
    have hY_nn : 0 ≤ Y := by
      refine mul_nonneg hδ_neg_eps_2_nn ?_
      exact Real.rpow_nonneg h_inner'_nn _
    have hZ_nn : 0 ≤ Z := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
      · exact Real.rpow_nonneg hδ_pos'.le _
      · exact Real.rpow_nonneg h_CF_nn _
      · exact Real.rpow_nonneg hδ_pos'.le _
      · exact Real.rpow_nonneg h_inner_nn _
    have hY_le_Z : Y ≤ Z := by
      have h1 :
          Y ≤ (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            (((2 : ℝ) ^ (1 - β / 2) * CFactual.toReal ^ (1 - β / 2)) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) :=
        mul_le_mul_of_nonneg_left hcard_chain_pow hδ_neg_eps_2_nn
      have h2 :
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            (((2 : ℝ) ^ (1 - β / 2) * CFactual.toReal ^ (1 - β / 2)) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) ≤
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            ((δ : ℝ) ^ (-(ε / 2)) *
              (CFactual.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hδ_neg_eps_2_nn
        have := mul_le_mul_of_nonneg_right hδ_slack hprod_nn
        nlinarith [this]
      have h3 :
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            ((δ : ℝ) ^ (-(ε / 2)) *
              (CFactual.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2))) = Z := by
        have h_pow : (δ : ℝ) ^ (-(ε / 2) - 2 * β) * (δ : ℝ) ^ (-(ε / 2)) =
            (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β) := by
          rw [← Real.rpow_add hδ_pos', ← Real.rpow_add hδ_pos']
          congr 1; ring
        rw [hZ_def]
        calc _ = ((δ : ℝ) ^ (-(ε / 2) - 2 * β) * (δ : ℝ) ^ (-(ε / 2))) *
              (CFactual.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) := by ring
          _ = ((δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β)) *
              (CFactual.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) := by rw [h_pow]
          _ = (δ : ℝ) ^ (-ε) * CFactual.toReal ^ (1 - β / 2) * (δ : ℝ) ^ (-2 * β) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by ring
      linarith [h1, h2, h3]
    have hY_enn := (multiplicity_bound_Y_enn_eq_ofReal hδ_pos' hβ2_nn s'.card
      (Module.finrank ℝ E) h_inner'_nn).trans (by rw [← hY_def])
    have hZ_enn : ENNReal.ofReal Z =
        (δ : ENNReal) ^ (-ε) * CFactual ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      rw [hZ_def]
      exact multiplicity_bound_Z_enn_eq_ofReal hδ_pos' hCF_ne_top hβ2_nn s.card
        (Module.finrank ℝ E) h_inner_nn
    calc ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.multiplicity s' (fun p ↦ (T' p).toShadedBody) := hmu_le
      _ ≤ (δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
            ((s'.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
          hmu_inner
      _ = ENNReal.ofReal Y := hY_enn
      _ ≤ ENNReal.ofReal Z := ENNReal.ofReal_le_ofReal hY_le_Z
      _ = (δ : ENNReal) ^ (-ε) * CFactual ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
          hZ_enn

/-- Memberwise-ball form of `Kakeya.FrostmanEstimate.multiplicity_bound`.

The canonical estimate asks for ball containment at every value of the ambient index type because
its random-copy construction evaluates the tube map outside the active finset.  A caller normally
only controls active indices.  On a nonempty family we totalize the map by one active tube; on the
empty family the conclusion is immediate. -/
theorem FrostmanEstimate.multiplicity_bound_of_mem {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
          (ConvexSpaceBody.frostmanConstant s (fun i ↦ (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) *
        (δ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^
          (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    FrostmanEstimate.multiplicity_bound (E := E) hβ_0 hβ_1 hn h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hball hED hfull
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  let i₀ : ι := hs.choose
  let T' : ι → ShadedTube δ E := fun i ↦ if i ∈ s then T i else T i₀
  have hi₀ : i₀ ∈ s := hs.choose_spec
  have hT' (i : ι) (hi : i ∈ s) : T' i = T i := by simp [T', hi]
  have hball' : ∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i
    by_cases hi : i ∈ s
    · simpa [hT' i hi] using hball i hi
    · simpa [T', hi] using hball i₀ hi₀
  have hED' : (s : Set ι).Pairwise
      (fun i j ↦ IsEssentiallyDistinct ((T' i).carrier) ((T' j).carrier)) := by
    intro i hi j hj hij
    simpa [hT' i hi, hT' j hj] using hED hi hj hij
  have hshadeSum : (∑ i ∈ s, volume (T' i).shade) = ∑ i ∈ s, volume (T i).shade := by
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
  have hcarrierSum : (∑ i ∈ s, volume (T' i).carrier) =
      ∑ i ∈ s, volume (T i).carrier := by
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
  have hunion : (⋃ i ∈ s, (T' i).shade) = ⋃ i ∈ s, (T i).shade := by
    apply Set.iUnion_congr
    intro i
    apply Set.iUnion_congr
    intro hi
    rw [hT' i hi]
  have hfullEq : ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody) =
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) := by
    rw [← ENNReal.coe_inj]
    rw [ShadedBody.fullness_def, ShadedBody.fullness_def, hshadeSum, hcarrierSum]
  have hfull' : ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody) ≥ δ ^ η := by
    rwa [hfullEq]
  have hbound := hδ s T' hball' hED' hfull'
  have hmultEq : ShadedBody.multiplicity s (fun i ↦ (T' i).toShadedBody) =
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hshadeSum, hunion]
  have hdensity (K : ConvexSpaceBody E) :
      densityIn s (fun i ↦ (T' i).toConvexSpaceBody) K =
        densityIn s (fun i ↦ (T i).toConvexSpaceBody) K := by
    change (∑ i ∈ s with (T' i).toConvexSpaceBody ≤ K, volume (T' i).carrier) /
        volume K.carrier =
      (∑ i ∈ s with (T i).toConvexSpaceBody ≤ K, volume (T i).carrier) /
        volume K.carrier
    congr 1
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
  have hfrostEq : ConvexSpaceBody.frostmanConstant s
      (fun i ↦ (T' i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall =
        ConvexSpaceBody.frostmanConstant s
          (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    unfold ConvexSpaceBody.frostmanConstant
    congr 1
    ext C
    simp only [Set.mem_setOf_eq, ConvexSpaceBody.IsFrostmanIn]
    constructor <;> intro hC K hK
    · simpa only [hdensity] using hC K hK
    · simpa only [hdensity] using hC K hK
  rwa [hmultEq, hfrostEq] at hbound

/-- **[GWZ, Lemma 3.9], uniformly in the Frostman constant over the range `C_F ≤ δ ^ (-θ)`.**

This is `Kakeya.FrostmanEstimate.multiplicity_bound` with the quantifier over the Frostman
constant `CF` moved *inside* the `∀ᶠ δ`, at the price of restricting `CF` to a range
`1 ≤ CF ≤ δ ^ (-θ)` whose exponent `θ > 0` is produced alongside `η` and depends only on `ε`
and `β` — never on the family.  This is the quantifier order that
`Kakeya.FrostmanEstimate.MultiplicityBoundUniform` asks for, over that range.

It is proved from `Kakeya.exists_randCF_translation_family_uniform`, the `CF`-uniform form of
[GWZ, Lemma 3.8], with `θ := min (η_mult / 4) 1` where `η_mult` is the exponent that
`Kakeya.FrostmanEstimate.ball2_version_edUpToMult` supplies at `ε / 2`.

**What separates this from `Kakeya.FrostmanEstimate.MultiplicityBoundUniform`.**  Three things,
all of them real:

1. *The range.*  `CF ≤ δ ^ (-θ)` cannot be dropped.  The construction of [GWZ, Lemma 3.8]
   translates the family `⌈CF⌉₊` times, and the resulting translate family has ED-multiplicity
   `Ω(CF)` for *every* admissible choice of translation vectors — a parallel-packing family of
   `⌈CF⌉₊` directions in a `δ ^ (1/2)`-cap already forces multiplicity `≥ c_n · ⌈CF⌉₊`.  Since
   `Kakeya.FrostmanEstimate.ball2_version_edUpToMult` charges the cap as a `δ ^ (-η)` loss, no
   `CF`-independent bound of this shape is available from that route.  Meanwhile `C_F` of an
   essentially distinct family of `ρ`-tubes in `B₁` runs up to a *fixed* negative power of `ρ`,
   and the complementary range `δ ^ (-θ) < CF` is not reachable by the crude counting bound
   either: closing it there would need `η ≳ 4`, whereas the smallness envelopes supply only
   small `η`.
2. *The ball hypothesis.*  This theorem assumes `∀ i, (T i).carrier ⊆ B₁`, whereas
   `MultiplicityBoundUniform` assumes only `∀ i ∈ s`.  Bridging the two is a routine
   reindexing along `{i // i ∈ s}`, but it is not done here.
3. *The conclusion constant.*  Here `CF` is a hypothesis and appears in the conclusion;
   `MultiplicityBoundUniform` puts `Kakeya.ConvexSpaceBody.frostmanConstIn` itself there.
   Specialising needs `1 ≤ frostmanConstIn` (available from
   `Kakeya.one_le_frostmanConstIn` for a family of positive density) together with finiteness
   of that constant. -/
theorem FrostmanEstimate.multiplicity_bound_uniform_upTo {β : ℝ} (_hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ θ > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ CF : ENNReal, 1 ≤ CF → CF ≤ (δ : ENNReal) ^ (-θ) →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall CF →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) *
        (δ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  have hn_pos : 0 < Module.finrank ℝ E := by linarith
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  obtain ⟨η_mult, hη_mult_pos, hKF_B2_mult⟩ :=
    FrostmanEstimate.ball2_version_edUpToMult (E := E) (by linarith) h (ε / 2)
      (by linarith)
  set c := min (η_mult / 2) (ε / 8) with hc_def
  have hc_pos : 0 < c := lt_min (by linarith) (by linarith)
  have hc_le_eta_mult_half : c ≤ η_mult / 2 := min_le_left _ _
  set θ : ℝ := min (η_mult / 4) 1 with hθ_def
  have hθ_pos : 0 < θ := lt_min (by linarith) one_pos
  have hθ_le_quarter : θ ≤ η_mult / 4 := min_le_left _ _
  have hθ_le_one : θ ≤ 1 := min_le_right _ _
  refine ⟨c, hc_pos, θ, hθ_pos, ?_⟩
  have hRandCF := nnreal_eventually_of_real_eventually
    (Kakeya.exists_randCF_translation_family_uniform (E := E) η_mult hη_mult_pos
      (η₀ := θ) hθ_pos hθ_le_quarter hθ_le_one)
  have hslack_event := nnreal_eventually_of_real_eventually
    ((tendsto_rpow_neg_nhdsGT_zero (by linarith : -(ε / 2) < 0)).eventually_ge_atTop
      ((2 : ℝ) ^ ((1 : ℝ) - β / 2)))
  filter_upwards [hKF_B2_mult, hRandCF, hslack_event,
    nnreal_eventually_of_real_eventually (p := fun δ => δ < 1)
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)),
    nnreal_eventually_of_real_eventually (p := fun δ => 0 < δ) self_mem_nhdsWithin]
    with δ hδ_KF_B2_mult hδ_randCF hδ_slack hδ_lt_one hδ_pos
  intro CF hCF1 hCF_range ι s T hB hED hfull hFrost
  have hδ_pos_R : (0 : ℝ) < (δ : ℝ) := hδ_pos
  have hpow_ne_top : ((δ : ENNReal)) ^ (-θ) ≠ ⊤ := by
    rw [← ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast hδ_pos_R.ne') (-θ)]
    exact ENNReal.coe_ne_top
  have hCF_ne_top : CF ≠ ⊤ := ne_top_of_le_ne_top hpow_ne_top hCF_range
  have hCF_toReal_ge_one : (1 : ℝ) ≤ CF.toReal := by
    simpa using ENNReal.toReal_mono hCF_ne_top hCF1
  have hCF_toReal_le : CF.toReal ≤ (δ : ℝ) ^ (-θ) := by
    have := ENNReal.toReal_mono hpow_ne_top hCF_range
    simpa [← ENNReal.toReal_rpow, ENNReal.coe_toReal] using this
  rcases eq_or_ne s ∅ with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  · have hδ_pos' : (0 : ℝ) < (δ : ℝ) := hδ_pos
    rw [show Real.toNNReal (δ : ℝ) = δ from Real.toNNReal_coe] at hδ_randCF
    have hfull_real : ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)) : ℝ)
        ≥ (δ : ℝ) ^ c := by
      simpa [NNReal.coe_rpow] using NNReal.coe_le_coe.mpr hfull
    have hfull_mult :
        ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)) : ℝ) ≥ (δ : ℝ) ^ η_mult :=
      le_trans (Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le
        (by linarith [hc_le_eta_mult_half])) hfull_real
    have hFrost' : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF.toReal) := by
      rwa [ENNReal.ofReal_toReal hCF_ne_top]
    obtain ⟨ι', s', T', M_cap, hcard_le, hM_cap_bd, hB', hED', hFrost'_out, hfull', hmu_le⟩ :=
      hδ_randCF CF.toReal hCF_toReal_ge_one hCF_toReal_le s T hB hED hFrost' hfull_mult
    have hfull'_NN :
        ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ δ ^ η_mult := by
      have := hfull'
      simp only [show ((δ : ℝ) ^ η_mult) = ((δ ^ η_mult : NNReal) : ℝ) by
        simp [NNReal.coe_rpow]] at this
      exact NNReal.coe_le_coe.mp this
    have hmu_inner :=
      hδ_KF_B2_mult s' T' M_cap hM_cap_bd hB' hED' hFrost'_out hfull'_NN
    have hCF_ceil_le_2CF : (⌈CF.toReal⌉₊ : ℝ) ≤ 2 * CF.toReal := by
      have := (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ CF.toReal)).le
      linarith
    have h_CF_nn : 0 ≤ CF.toReal := by linarith
    have hβ2_nn : 0 ≤ (1 : ℝ) - β / 2 := by linarith
    have hδpow_nn : 0 ≤ (δ : ℝ) ^ (Module.finrank ℝ E - 1) := pow_nonneg hδ_pos'.le _
    have h_inner_nn : 0 ≤ ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by positivity
    have h_inner'_nn : 0 ≤ ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by positivity
    have hcard_chain :
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ≤
          ((2 : ℝ) * CF.toReal) * ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) := by
      have h1 : (s'.card : ℝ) ≤ 2 * CF.toReal * (s.card : ℝ) :=
        hcard_le.trans (mul_le_mul_of_nonneg_right hCF_ceil_le_2CF (Nat.cast_nonneg _))
      have := mul_le_mul_of_nonneg_right h1 hδpow_nn
      linarith [this]
    have hcard_chain_pow :
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) ≤
          ((2 : ℝ) ^ (1 - β / 2) * CF.toReal ^ (1 - β / 2)) *
            ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      have h_pow_le := Real.rpow_le_rpow h_inner'_nn hcard_chain hβ2_nn
      rwa [Real.mul_rpow (by positivity) h_inner_nn,
        Real.mul_rpow (by norm_num) h_CF_nn] at h_pow_le
    have hδ_neg_eps_2_nn : 0 ≤ (δ : ℝ) ^ (-(ε / 2) - 2 * β) := Real.rpow_nonneg hδ_pos'.le _
    have hprod_nn : 0 ≤ CF.toReal ^ (1 - β / 2) *
        ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by positivity
    -- Real-valued bound: s'.card * δ^(n-1) ≤... (lifted to ENNReal below).
    set Y : ℝ := (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
        ((s'.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) with hY_def
    set Z : ℝ := (δ : ℝ) ^ (-ε) * CF.toReal ^ (1 - β / 2) * (δ : ℝ) ^ (-2 * β) *
        ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) with hZ_def
    have hY_nn : 0 ≤ Y := by
      refine mul_nonneg hδ_neg_eps_2_nn ?_
      exact Real.rpow_nonneg h_inner'_nn _
    have hZ_nn : 0 ≤ Z := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
      · exact Real.rpow_nonneg hδ_pos'.le _
      · exact Real.rpow_nonneg h_CF_nn _
      · exact Real.rpow_nonneg hδ_pos'.le _
      · exact Real.rpow_nonneg h_inner_nn _
    have hY_le_Z : Y ≤ Z := by
      have h1 :
          Y ≤ (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            (((2 : ℝ) ^ (1 - β / 2) * CF.toReal ^ (1 - β / 2)) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) :=
        mul_le_mul_of_nonneg_left hcard_chain_pow hδ_neg_eps_2_nn
      have h2 :
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            (((2 : ℝ) ^ (1 - β / 2) * CF.toReal ^ (1 - β / 2)) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) ≤
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            ((δ : ℝ) ^ (-(ε / 2)) *
              (CF.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hδ_neg_eps_2_nn
        have := mul_le_mul_of_nonneg_right hδ_slack hprod_nn
        nlinarith [this]
      have h3 :
          (δ : ℝ) ^ (-(ε / 2) - 2 * β) *
            ((δ : ℝ) ^ (-(ε / 2)) *
              (CF.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2))) = Z := by
        have h_pow : (δ : ℝ) ^ (-(ε / 2) - 2 * β) * (δ : ℝ) ^ (-(ε / 2)) =
            (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β) := by
          rw [← Real.rpow_add hδ_pos', ← Real.rpow_add hδ_pos']
          congr 1; ring
        rw [hZ_def]
        calc _ = ((δ : ℝ) ^ (-(ε / 2) - 2 * β) * (δ : ℝ) ^ (-(ε / 2))) *
              (CF.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) := by ring
          _ = ((δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β)) *
              (CF.toReal ^ (1 - β / 2) *
                ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)) := by rw [h_pow]
          _ = (δ : ℝ) ^ (-ε) * CF.toReal ^ (1 - β / 2) * (δ : ℝ) ^ (-2 * β) *
              ((s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by ring
      linarith [h1, h2, h3]
    have hY_enn := (multiplicity_bound_Y_enn_eq_ofReal hδ_pos' hβ2_nn s'.card
      (Module.finrank ℝ E) h_inner'_nn).trans (by rw [← hY_def])
    have hZ_enn : ENNReal.ofReal Z =
        (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      rw [hZ_def]
      exact multiplicity_bound_Z_enn_eq_ofReal hδ_pos' hCF_ne_top hβ2_nn s.card
        (Module.finrank ℝ E) h_inner_nn
    calc ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.multiplicity s' (fun i ↦ (T' i).toShadedBody) := hmu_le
      _ ≤ (δ : ENNReal) ^ (-(ε / 2) - 2 * β) *
            ((s'.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
          hmu_inner
      _ = ENNReal.ofReal Y := hY_enn
      _ ≤ ENNReal.ofReal Z := ENNReal.ofReal_le_ofReal hY_le_Z
      _ = (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
          hZ_enn

/-- **A family of positive density has Frostman constant at least `1`.**

Testing `ConvexSpaceBody.IsFrostmanIn s W K C` at `K' = K` reads `Δ(s, W, K) ≤ C · Δ(s, W, K)`,
and `Δ(s, W, K)` is always finite, so a nonzero density forces `1 ≤ C` for every admissible `C`.
Taking the infimum bounds `C_F(𝕍, K)` from below.

This is the clause "`C_F(𝕍, B₁) ≥ 1` for a nonempty family" used in the bounded-tube-scale
regime of blueprint `lem:genKFAuxScale`; note that it genuinely needs the density hypothesis,
since `Kakeya.ConvexSpaceBody.frostmanConstIn_empty` gives the value `0` at the empty family. -/
theorem one_le_frostmanConstIn {ι : Type*} {s : Finset ι}
    {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} (h : 0 < densityIn s W K) :
    1 ≤ ConvexSpaceBody.frostmanConstIn s W K := by
  exact le_sInf (fun C hC => by
    have hd : densityIn s W K ≤ C * densityIn s W K := hC K le_rfl
    exact (ENNReal.mul_le_mul_iff_right h.ne' (densityIn_ne_top s W K)).1 (by
      simpa [mul_comm, mul_one] using hd))

/-- **Padding a crude bound out to the shape of blueprint `eq:genKFAuxScale`.**

The two crude regimes of `lem:genKFAuxScale` both end with `μ ≤ |s|` together with an estimate
of `|s|` against `D · X ^ a`, where `D` is the loss `δ ^ (-ε)`, `X` is `|s| ρ ^ (n-1)` and
`a = 1 - β/2`.  The remaining two factors of the target — the Frostman constant to the power `a`
and `ρ ^ (-2β)` — are both at least `1`, so they can simply be inserted.  Keeping this step
separate from the geometry means each regime only has to produce its own `hN`. -/
private lemma mult_le_pad {μ N F R X D : ENNReal} {a : ℝ} (hF : 1 ≤ F) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (hμN : μ ≤ N) (hN : N ≤ D * X ^ a) :
    μ ≤ D * F ^ a * R * X ^ a := by
  have hFpow : (1 : ENNReal) ≤ F ^ a := by
    calc
      (1 : ENNReal) = F ^ (0 : ℝ) := by rw [ENNReal.rpow_zero]
      _ ≤ F ^ a := ENNReal.rpow_le_rpow_of_exponent_le hF ha
  calc
    μ ≤ N := hμN
    _ ≤ D * X ^ a := hN
    _ = D * 1 * 1 * X ^ a := by ring
    _ ≤ D * F ^ a * R * X ^ a := by gcongr

/-- **The bounded-tube-scale regime of blueprint `lem:genKFAuxScale`, unconditionally.**

If the tube scale `ρ` stays above a fixed `ρ₀ > 0`, the estimate of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` holds with no appeal to `K_F(β)` at all.
Indeed `μ(𝕍, Z) ≤ |s|`, and `|s|` is bounded by `C(n) ρ₀ ^ (-2n)` by
`Tube.card_le_of_EssDistinct`, while the right-hand side is at least
`δ ^ (-ε) · (ρ₀ ^ (n-1)) ^ (1 - β/2)` because `C_F(𝕍, B₁) ≥ 1` for a nonempty family, `|s| ≥ 1`,
and `ρ ^ (-2β) ≥ 1` for `ρ ≤ 1` and `β ≥ 0`.  The loss `δ ^ (-ε)` then absorbs the ratio of the
two constants once `δ` is small, so the threshold on `δ` depends only on `ε`, `β`, `n` and `ρ₀`
— and in particular not on the family. -/
theorem FrostmanEstimate.multiplicity_le_of_bounded_tube_scale {β : ℝ} (hβ_0 : 0 ≤ β)
    (hβ_1 : β ≤ 1) (hn : 1 < Module.finrank ℝ E) {ε : ℝ} (hε : 0 < ε)
    {ρ₀ : NNReal} (hρ₀ : 0 < ρ₀) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ ρ : NNReal, ρ₀ ≤ ρ → ρ ≤ 1 →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  have hn_pos : 0 < Module.finrank ℝ E := by omega
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  set n := Module.finrank ℝ E with hn_def
  set D : ℝ := Tube.card_le_of_EssDistinct.C n with hD_def
  have hD_pos : 0 < D := by
    rw [hD_def]
    exact Tube.card_le_of_EssDistinct.C_pos
  set c₁ : ℝ := ((ρ₀ : ℝ) ^ (n - 1)) ^ (1 - β / 2) with hc₁_def
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]
    exact Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast hρ₀) (n - 1)) (1 - β / 2)
  set N₀ : ℝ := D * (1 / (ρ₀ : ℝ)) ^ (2 * n) with hN₀_def
  have hN₀_pos : 0 < N₀ := by
    rw [hN₀_def]
    exact mul_pos hD_pos (pow_pos (one_div_pos.mpr (by exact_mod_cast hρ₀)) (2 * n))
  have hN₀_div_c₁_pos : 0 < N₀ / c₁ := div_pos hN₀_pos hc₁_pos
  obtain ⟨δ₀, hδ₀_pos, hδ₀_threshold⟩ :=
    exists_threshold_ofReal_le_rpow (C := N₀ / c₁) hN₀_div_c₁_pos (a := ε) hε
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₀_pos)]
    with δ hδ_pos hδ_lt_δ₀
  intro ρ hρ₀_le_ρ hρ_le_1 ι s T hs hball hED
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hρ₀ hρ₀_le_ρ
  have hδ_threshold : ENNReal.ofReal (N₀ / c₁) ≤ (δ : ENNReal) ^ (-ε) :=
    hδ₀_threshold δ hδ_pos hδ_lt_δ₀
  -- counting bound: (s.card : ℝ) ≤ N₀
  have hcard_le : (s.card : ℝ) ≤ D * (1 / (ρ : ℝ)) ^ (2 * n) := by
    rw [hD_def]
    exact Tube.card_le_of_EssDistinct hρ_pos 1 s (fun i => (T i).toTube) hball hED
  have h_pow_mono : (1 / (ρ : ℝ)) ^ (2 * n) ≤ (1 / (ρ₀ : ℝ)) ^ (2 * n) := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (1 / (ρ : ℝ)))
      (one_div_le_one_div_of_le (by exact_mod_cast hρ₀) hρ₀_le_ρ) (2 * n)
  have hcard_le_N₀ : (s.card : ℝ) ≤ N₀ := by
    calc
      (s.card : ℝ) ≤ D * (1 / (ρ : ℝ)) ^ (2 * n) := hcard_le
      _ ≤ D * (1 / (ρ₀ : ℝ)) ^ (2 * n) := mul_le_mul_of_nonneg_left h_pow_mono hD_pos.le
      _ = N₀ := by rw [hN₀_def]
  -- Frostman constant ≥ 1
  set FC : ENNReal := ConvexSpaceBody.frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall with hFC_def
  have hFC1 : (1 : ENNReal) ≤ FC := by
    rw [hFC_def]
    apply one_le_frostmanConstIn
    rw [densityIn_pos_iff]
    rcases hs with ⟨i₀, hi₀⟩
    refine ⟨i₀, hi₀, ?_, ?_⟩
    · have hvol_lower_pos : (0 : ENNReal) <
        (Tube.le_volume.c n : ENNReal) * (ρ : ENNReal) ^ (n - 1) := by
        exact_mod_cast (mul_pos (Tube.le_volume.c_pos n) (pow_pos hρ_pos (n - 1)))
      have hvol : 0 < volume (T i₀).carrier :=
        lt_of_lt_of_le hvol_lower_pos (Tube.le_volume (T i₀).toTube)
      simpa using hvol
    · change (T i₀).toConvexSpaceBody.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i₀ hi₀
  -- lower bounds for the right-hand side
  have hβ2_nn : 0 ≤ (1 : ℝ) - β / 2 := by linarith
  have hβ2_pos : 0 < (1 : ℝ) - β / 2 := by linarith
  have hFC_pow : (1 : ENNReal) ≤ FC ^ (1 - β / 2) := ENNReal.one_le_rpow hFC1 hβ2_pos
  have hρ_pow : (1 : ENNReal) ≤ (ρ : ENNReal) ^ (-2 * β) := by
    rw [show -2 * β = -(2 * β) by ring]
    rw [ENNReal.rpow_neg]
    exact ENNReal.one_le_inv.mpr (ENNReal.rpow_le_one (by exact_mod_cast hρ_le_1) (by linarith))
  have hcard1 : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast (Finset.one_le_card.mpr hs)
  have hρ₀_le_ρ_pow : (ρ₀ : ENNReal) ^ (n - 1) ≤ (ρ : ENNReal) ^ (n - 1) := by
    exact pow_le_pow_left₀ zero_le (by exact_mod_cast hρ₀_le_ρ) (n - 1)
  have h_card_ρ : (ρ₀ : ENNReal) ^ (n - 1) ≤
      (s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1) := by
    calc
      (ρ₀ : ENNReal) ^ (n - 1) = 1 * (ρ₀ : ENNReal) ^ (n - 1) := by rw [one_mul]
      _ ≤ (s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1) :=
          mul_le_mul hcard1 hρ₀_le_ρ_pow zero_le zero_le
  have hc₁_enn : ENNReal.ofReal c₁ = ((ρ₀ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
    rw [hc₁_def]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_pow (by exact_mod_cast hρ₀.le)]
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos (by exact_mod_cast hρ₀) (n - 1))]
  have h_c₁_le : ENNReal.ofReal c₁ ≤
      FC ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
    calc
      ENNReal.ofReal c₁ = ((ρ₀ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := hc₁_enn
      _ ≤ ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) :=
          ENNReal.rpow_le_rpow h_card_ρ hβ2_nn
      _ = 1 * 1 * ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by simp
      _ ≤ FC ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
            ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
          exact mul_le_mul (mul_le_mul hFC_pow hρ_pow zero_le zero_le) le_rfl zero_le zero_le
  -- assemble
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (s.card : ENNReal) := ShadedBody.multiplicity_le_card s (fun i ↦ (T i).toShadedBody)
    _ = ENNReal.ofReal (s.card : ℝ) := by rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal N₀ := ENNReal.ofReal_le_ofReal hcard_le_N₀
    _ = ENNReal.ofReal (N₀ / c₁) * ENNReal.ofReal c₁ := by
        rw [mul_comm, ← ENNReal.ofReal_mul hc₁_pos.le]
        congr 1
        field_simp [hc₁_pos.ne']
    _ ≤ (δ : ENNReal) ^ (-ε) * ENNReal.ofReal c₁ := by
        exact mul_le_mul_left hδ_threshold (ENNReal.ofReal c₁)
    _ ≤ (δ : ENNReal) ^ (-ε) * (FC ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2)) := by
        exact mul_le_mul_right h_c₁_le ((δ : ENNReal) ^ (-ε))
    _ = (δ : ENNReal) ^ (-ε) * FC ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
        ac_rfl

/-- **[GWZ, Lemma 3.9] with the Frostman constant as a conclusion factor** (blueprint `genKF`).

This is blueprint Lemma `genKF` *as the blueprint states it*: the Frostman constant
`C_F(𝕍, B₁)` of the family is a factor in the conclusion, and the smallness threshold for the
tube scale is allowed to depend on `ε` and `β` only — in particular not on the family, hence not
on its Frostman constant.

It is strictly stronger than `Kakeya.FrostmanEstimate.multiplicity_bound`, which quantifies its
constant `CF` *before* the `∀ᶠ δ` and therefore lets the threshold depend on `CF`.  The
difference is not cosmetic.  `Kakeya.FrostmanEstimate.multiplicity_bound` is proved through
`Kakeya.exists_randCF_translation_family`, whose smallness envelopes are polynomial in `CF` (the
`J`-fold random translate family is bounded essentially-distinct only up to multiplicity
`⌈CF⌉ · C_pack`, and that cap is charged downstream as a `δ ^ (-η)` loss), so that route is
available only for `CF` below a small fixed power of the scale.  The Frostman constant of an
essentially distinct family of `ρ`-tubes in `B₁` ranges up to a *fixed* negative power of `ρ`,
so the missing range is not reachable by the crude counting bound either.

Separating the two forms is the point: `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`
needs this uniform form and provably cannot be assembled from the `CF`-dependent one.  See
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_uniform`.

This statement is **not** proved.  What *is* proved is
`Kakeya.FrostmanEstimate.MultiplicityBoundUniformUpTo`, which is this statement plus the single
extra hypothesis `C_F(𝕍, B₁) ≤ ρ ^ (-θ)`; that extra hypothesis is the entire gap. -/
def FrostmanEstimate.MultiplicityBoundUniform (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (ρ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (ρ : ENNReal) ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (ρ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)

/-- **Blueprint `genKF`, uniform in the Frostman constant over the range `C_F ≤ ρ ^ (-θ)`.**

This is `Kakeya.FrostmanEstimate.MultiplicityBoundUniform` *verbatim*, with one extra hypothesis:
the exponent `θ > 0` produced alongside `η`, likewise depending only on `ε` and `β` and never on
the family, restricts the estimate to families whose Frostman constant satisfies
`C_F(𝕍, B₁) ≤ ρ ^ (-θ)`.  Nothing else differs — same quantifier order, same fullness
hypothesis, same conclusion with `C_F(𝕍, B₁)` itself as the conclusion factor.

This form is **proved**, as `Kakeya.FrostmanEstimate.multiplicityBoundUniformUpTo` — and so is
the unrestricted `Kakeya.FrostmanEstimate.MultiplicityBoundUniform`, as
`Kakeya.FrostmanEstimate.multiplicityBoundUniform`, so the extra hypothesis is **never needed**.
It is kept as the honest ceiling of the *translation* construction of GWZ Lemma 3.8, whose
ED-multiplicity cap is `Ω(C_F)` for geometric reasons; the *rigid-motion* construction
`Kakeya.exists_randCF_rigid_family` has a `C_F`-independent cap and is what removes the
restriction.  See the docstring of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` for the full account. -/
def FrostmanEstimate.MultiplicityBoundUniformUpTo (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ θ > (0 : ℝ), ∀ᶠ (ρ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (ρ : ENNReal) ^ η →
      ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ≤ (ρ : ENNReal) ^ (-θ) →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (ρ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)

/-- **Reindexing the multiplicity along `Finset.attach`.**  Both the numerator sum and the
denominator union of `ShadedBody.multiplicity` range over exactly the same bodies after
`s` is replaced by `s.attach` and the family is precomposed with `Subtype.val`.

This is the bookkeeping that turns a hypothesis `∀ i ∈ s, P i` into a hypothesis `∀ i, P i`
about a totally defined family, as needed to feed
`Kakeya.FrostmanEstimate.multiplicity_bound_uniform_upTo`. -/
private lemma multiplicity_attach {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.multiplicity s.attach (fun i ↦ V i.1) = ShadedBody.multiplicity s V := by
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  congr 1
  · exact Finset.sum_attach s (fun i => volume (V i).shade)
  · congr 1
    ext x
    simp

/-- **Reindexing the fullness along `Finset.attach`**; companion of `Kakeya.multiplicity_attach`,
proved the same way from `ShadedBody.fullness_def`. -/
private lemma fullness_attach {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness s.attach (fun i ↦ V i.1) = ShadedBody.fullness s V := by
  rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def]
  congr 1
  · exact Finset.sum_attach s (fun i => volume (V i).shade)
  · exact Finset.sum_attach s (fun i => volume (V i).carrier)

/-- **Blueprint `genKF` in its uniform form, on the range `C_F ≤ ρ ^ (-θ)`** — that is,
`Kakeya.FrostmanEstimate.MultiplicityBoundUniformUpTo` holds under the partial Frostman
estimate at `β`.

The whole content is `Kakeya.FrostmanEstimate.multiplicity_bound_uniform_upTo`; this theorem
closes the two bookkeeping gaps between that statement and
`Kakeya.FrostmanEstimate.MultiplicityBoundUniform`:

* *The ball binder.*  `multiplicity_bound_uniform_upTo` asks for `∀ i, (T i).carrier ⊆ B₁`, a
  condition on the *total* family, while the target only assumes it for `i ∈ s`.  The two are
  bridged by reindexing along `Finset.attach`, where the restriction of `T` is total by
  construction; `Kakeya.multiplicity_attach`, `Kakeya.fullness_attach`,
  `Finset.card_attach` and `ConvexSpaceBody.IsFrostmanIn.reindex` transport the four
  hypotheses and the conclusion back and forth.
* *The conclusion constant.*  `multiplicity_bound_uniform_upTo` takes the Frostman constant
  `CF` as a hypothesis and puts it in the conclusion; here it is instantiated at
  `C_F(𝕍, B₁)` itself.  That instantiation needs `1 ≤ C_F(𝕍, B₁)`, which is
  `Kakeya.one_le_frostmanConstIn` applied to the positive density of a nonempty family of
  tubes inside `B₁`, and it needs `𝕍` to be `C_F(𝕍, B₁)`-Frostman, which is
  `Kakeya.ConvexSpaceBody.isFrostmanIn_frostmanConstIn` (the defining infimum is attained).
  Finiteness of `C_F(𝕍, B₁)` is not a separate obligation: it follows from the range
  hypothesis `C_F(𝕍, B₁) ≤ ρ ^ (-θ)`.

What is *not* closed here is the range hypothesis itself; see
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`. -/
theorem FrostmanEstimate.multiplicityBoundUniformUpTo {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    FrostmanEstimate.MultiplicityBoundUniformUpTo.{v} E β := by
  intro ε hε
  have hn_pos : 0 < Module.finrank ℝ E := by omega
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  obtain ⟨η, hη, θ, hθ, hev⟩ := multiplicity_bound_uniform_upTo (E := E) hβ_0 hβ_1 hn h ε hε
  refine ⟨η, hη, θ, hθ, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρ_pos
  intro ι s T hne hball hED hfull hrange
  let ι' : Type v := {i : ι // i ∈ s}
  let s' : Finset ι' := s.attach
  let T' : ι' → ShadedTube ρ E := fun i ↦ T i.1
  have hball' : ∀ i : ι', (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i
    exact hball i.1 i.2
  have hED' : (s' : Set ι').Pairwise
      (fun i j ↦ IsEssentiallyDistinct ((T' i).carrier) ((T' j).carrier)) := by
    intro i hi j hj hij
    exact hED (Finset.mem_coe.mpr i.2) (Finset.mem_coe.mpr j.2) (fun h => hij (Subtype.ext h))
  have hfull' : ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ ρ ^ η := by
    change ShadedBody.fullness s.attach (fun i : {x // x ∈ s} ↦ (T i.1).toShadedBody) ≥ ρ ^ η
    rw [@fullness_attach E _ _ _ _ _ ι s (fun i ↦ (T i).toShadedBody)]
    change (ρ ^ η : NNReal) ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
    rw [← ENNReal.coe_le_coe]
    rw [ENNReal.coe_rpow_of_ne_zero hρ_pos.ne' η]
    exact hfull
  set FC : ENNReal := ConvexSpaceBody.frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall with hFC_def
  have hFC1 : (1 : ENNReal) ≤ FC := by
    rw [hFC_def]
    apply one_le_frostmanConstIn
    rw [densityIn_pos_iff]
    rcases hne with ⟨i₀, hi₀⟩
    refine ⟨i₀, hi₀, ?_, ?_⟩
    · have hvol_lower_pos : (0 : ENNReal) <
        (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
          (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
        exact_mod_cast (mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E))
          (pow_pos hρ_pos (Module.finrank ℝ E - 1)))
      have hvol : 0 < volume (T i₀).carrier :=
        lt_of_lt_of_le hvol_lower_pos (Tube.le_volume (T i₀).toTube)
      simpa using hvol
    · change (T i₀).toConvexSpaceBody.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i₀ hi₀
  have hFrost : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall FC :=
    ConvexSpaceBody.isFrostmanIn_frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
  have hbij : Set.BijOn Subtype.val (s.attach : Set ι') (s : Set ι) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      exact Finset.mem_coe.mpr a.2
    · intro a ha b hb h
      exact Subtype.ext h
    · intro b hb
      have hb' : b ∈ s := Finset.mem_coe.mp hb
      exact ⟨⟨b, hb'⟩, Finset.mem_coe.mpr (Finset.mem_attach s ⟨b, hb'⟩), rfl⟩
  have hFrost' : IsFrostmanIn s' (fun i ↦ (T' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall FC := by
    change IsFrostmanIn s.attach ((fun i ↦ (T i).toConvexSpaceBody) ∘ Subtype.val)
      ConvexSpaceBody.closedUnitBall FC
    exact (ConvexSpaceBody.IsFrostmanIn.reindex (s := s) (W := fun i ↦ (T i).toConvexSpaceBody)
      (K := ConvexSpaceBody.closedUnitBall) (C := FC) (t := s.attach) (e := Subtype.val)
      (he := hbij)).mpr hFrost
  have hmu := hρ FC hFC1 (by simpa [hFC_def] using hrange) s' T' hball' hED' hfull' hFrost'
  change ShadedBody.multiplicity s.attach (fun i : {x // x ∈ s} ↦ (T i.1).toShadedBody) ≤
      (ρ : ENNReal) ^ (-ε) * FC ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
      ((s.attach.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) at hmu
  rw [@multiplicity_attach E _ _ _ _ _ ι s (fun i ↦ (T i).toShadedBody)] at hmu
  rw [Finset.card_attach] at hmu
  simpa [hFC_def] using hmu

/-- **Blueprint `genKF`, uniform in the Frostman constant — the unrestricted form.**

This is `Kakeya.FrostmanEstimate.MultiplicityBoundUniform`, the hypothesis that
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_uniform` consumes.

It is `Kakeya.FrostmanEstimate.multiplicity_bound` with the ball hypothesis relaxed from `∀ i` to
`∀ i ∈ s`, and nothing else.  In particular there is **no** difference of quantifier order: GWZ
Lemma 3.9 places the Frostman constant in its *conclusion*, after the family, so its `η` and its
`δ`-threshold depend on `ε` and `β` only — that is the content of blueprint
`note:genKFConstantPlacement` — and the two spellings of the constant agree by
`Kakeya.ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant`, which is `rfl`.

The uniformity is what the *rigid-motion* form of [GWZ, Lemma 3.8],
`Kakeya.exists_randCF_rigid_family`, buys: its ED-multiplicity cap is `rigidMED = O(log (1/δ))`,
independent of the Frostman constant, which is exactly what replaced the translation-only cap
`⌈C_F⌉₊ · C_pack_ext + 1` of `Kakeya.exists_randCF_translation_family`.
`Kakeya.FrostmanEstimate.multiplicity_bound` is proved from the rigid form with its `δ`-threshold
fixed by `filter_upwards` *before* the family is introduced, so it is already family-uniform, and
the range restriction `C_F ≤ ρ ^ (-θ)` that
`Kakeya.FrostmanEstimate.MultiplicityBoundUniformUpTo` carries — a restriction forced by the
translation route alone — is not needed here.

Proof: reindex along `Finset.attach`, exactly as in
`Kakeya.FrostmanEstimate.multiplicityBoundUniform_upTo_of_uniform_upTo`'s companion
`Kakeya.FrostmanEstimate.multiplicityBoundUniformUpTo`, but with no range hypothesis and no
Frostman hypothesis to transport. -/
theorem FrostmanEstimate.multiplicityBoundUniform {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    FrostmanEstimate.MultiplicityBoundUniform.{v} E β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := FrostmanEstimate.multiplicity_bound (E := E) hβ_0 hβ_1 hn h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρ_pos
  intro ι s T _hne hball hED hfull
  let ι' : Type v := {i : ι // i ∈ s}
  let s' : Finset ι' := s.attach
  let T' : ι' → ShadedTube ρ E := fun i ↦ T i.1
  have hball' : ∀ i : ι', (T' i).carrier ⊆ Metric.closedBall 0 1 := fun i ↦ hball i.1 i.2
  have hED' : (s' : Set ι').Pairwise
      (fun i j ↦ IsEssentiallyDistinct ((T' i).carrier) ((T' j).carrier)) := by
    intro i _hi j _hj hij
    exact hED (Finset.mem_coe.mpr i.2) (Finset.mem_coe.mpr j.2) (fun hv => hij (Subtype.ext hv))
  have hfull' : ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ ρ ^ η := by
    change ShadedBody.fullness s.attach (fun i : {x // x ∈ s} ↦ (T i.1).toShadedBody) ≥ ρ ^ η
    rw [@fullness_attach E _ _ _ _ _ ι s (fun i ↦ (T i).toShadedBody)]
    change (ρ ^ η : NNReal) ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero hρ_pos.ne' η]
    exact hfull
  have hbij : Set.BijOn Subtype.val (s.attach : Set ι') (s : Set ι) := by
    refine ⟨fun a _ ↦ Finset.mem_coe.mpr a.2, fun a _ b _ hab ↦ Subtype.ext hab, ?_⟩
    intro b hb
    have hb' : b ∈ s := Finset.mem_coe.mp hb
    exact ⟨⟨b, hb'⟩, Finset.mem_coe.mpr (Finset.mem_attach s ⟨b, hb'⟩), rfl⟩
  have hconst : ConvexSpaceBody.frostmanConstant s' (fun i ↦ (T' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
      = ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall := by
    rw [← ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant]
    exact ConvexSpaceBody.frostmanConstIn_reindex (W := fun i ↦ (T i).toConvexSpaceBody)
      (K := ConvexSpaceBody.closedUnitBall) hbij
  have hmu := hρ s' T' hball' hED' hfull'
  rw [hconst] at hmu
  change ShadedBody.multiplicity s.attach (fun i : {x // x ∈ s} ↦ (T i.1).toShadedBody) ≤ _ at hmu
  rw [@multiplicity_attach E _ _ _ _ _ ι s (fun i ↦ (T i).toShadedBody), Finset.card_attach] at hmu
  exact hmu

/-- **The deep-auxiliary-scale regime of blueprint `lem:genKFAuxScale`, unconditionally.**

The regime in which the tube scale `ρ` is small but the auxiliary scale `δ` is so much smaller
that the loss `δ ^ (-ε)` alone already pays for the whole estimate.  Precisely: for every
threshold `ρ₀ < 1` there is an exponent `C > 0` such that `δ < ρ ^ C` suffices, with no further
smallness hypothesis on `δ` and no appeal to `K_F(β)`.

Quantitatively, `μ ≤ |s| ≤ C(n) ρ ^ (-2n)` reduces the claim to
`|s| ^ (β/2) ≤ δ ^ (-ε) ρ ^ ((n-1)(1-β/2))`, and `δ < ρ ^ C` turns the loss into `ρ ^ (-Cε)`;
choosing `C` so that `Cε - (n-1)(1-β/2) - nβ` is large enough that `ρ₀` raised to its negative
dominates `C(n) ^ (β/2)` closes it, using `ρ ≤ ρ₀ < 1`.

**This regime is missing from the blueprint.**  The blueprint proof of `lem:genKFAuxScale`
splits into two regimes only, and in the small-tube-scale one derives the fullness hypothesis
`λ ≥ ρ ^ η` of blueprint `genKF` from `λ ≥ δ ^ η` together with `δ ≤ ρ ≤ 1`.  That implication
runs the wrong way: for `η > 0` the map `t ↦ t ^ η` is increasing, so `δ ≤ ρ` gives
`δ ^ η ≤ ρ ^ η` and `λ ≥ δ ^ η` is the *weaker* hypothesis, not the stronger one.  The
three-regime split used in
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_uniform` — `ρ ^ C ≤ δ`, `δ < ρ ^ C` with
`ρ ≤ ρ₀`, and `ρ₀ ≤ ρ` — repairs the gap, at the cost of rescaling `η` by `C`. -/
theorem FrostmanEstimate.multiplicity_le_of_deep_aux_scale {β : ℝ} (hβ_0 : 0 ≤ β)
    (hβ_1 : β ≤ 1) (hn : 1 < Module.finrank ℝ E) {ε : ℝ} (hε : 0 < ε)
    {ρ₀ : NNReal} (hρ₀ : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) :
    ∃ C > (0 : ℝ),
    ∀ δ ρ : NNReal, 0 < δ → δ ≤ ρ → ρ ≤ ρ₀ → (δ : ℝ) < (ρ : ℝ) ^ C →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  have hn_pos : 0 < Module.finrank ℝ E := by omega
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  set n := Module.finrank ℝ E with hn_def
  set D₀ : ℝ := Tube.card_le_of_EssDistinct.C n with hD₀_def
  have hD₀_pos : 0 < D₀ := by
    rw [hD₀_def]
    exact Tube.card_le_of_EssDistinct.C_pos
  set a : ℝ := 1 - β / 2 with ha_def
  have ha_pos : 0 < a := by linarith
  have ha_nn : 0 ≤ a := ha_pos.le
  have hβ2_nn : 0 ≤ β / 2 := by positivity
  have hρ₀_R_pos : (0 : ℝ) < (ρ₀ : ℝ) := by exact_mod_cast hρ₀
  have hρ₀_R_lt : (ρ₀ : ℝ) < 1 := by exact_mod_cast hρ₀1
  have hρ₀_R_nonneg : 0 ≤ (ρ₀ : ℝ) := hρ₀_R_pos.le
  -- an auxiliary exponent G with D₀^(β/2) ≤ (ρ₀)^(-G)
  have hlog_pos : 0 < Real.log (1 / (ρ₀ : ℝ)) := by
    have h_gt_one : (1 : ℝ) < 1 / (ρ₀ : ℝ) := by
      rw [one_lt_div hρ₀_R_pos]
      exact hρ₀_R_lt
    exact Real.log_pos h_gt_one
  have hlog_ne : Real.log (1 / (ρ₀ : ℝ)) ≠ 0 := ne_of_gt hlog_pos
  set G₀ : ℝ := ((β / 2) * Real.log D₀) / Real.log (1 / (ρ₀ : ℝ)) with hG₀_def
  set G : ℝ := max 1 G₀ with hG_def
  have hG_pos : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_left 1 G₀)
  have hG₀_le_G : G₀ ≤ G := le_max_right 1 G₀
  have hD₀pow_pos : 0 < D₀ ^ (β / 2) := Real.rpow_pos_of_pos hD₀_pos (β / 2)
  have hlog_inv : Real.log (1 / (ρ₀ : ℝ)) = -Real.log (ρ₀ : ℝ) := by
    rw [one_div, Real.log_inv]
  have hG₀_log_eq : Real.log ((ρ₀ : ℝ) ^ (-G₀)) = Real.log (D₀ ^ (β / 2)) := by
    rw [Real.log_rpow hρ₀_R_pos, Real.log_rpow hD₀_pos, hG₀_def]
    field_simp [hlog_ne]
    rw [hlog_inv]
    ring
  have hG₀_eq : (ρ₀ : ℝ) ^ (-G₀) = D₀ ^ (β / 2) := by
    refine le_antisymm ?_ ?_
    · exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hρ₀_R_pos (-G₀)) hD₀pow_pos).mp
        (le_of_eq hG₀_log_eq)
    · exact (Real.log_le_log_iff hD₀pow_pos (Real.rpow_pos_of_pos hρ₀_R_pos (-G₀))).mp
        (le_of_eq hG₀_log_eq.symm)
  have hrpow_inv : ∀ x : ℝ, 0 < x → x ^ (-G) = (1 / x) ^ G := by
    intro x hx
    rw [Real.rpow_neg hx.le, ← Real.inv_rpow hx.le, ← one_div]
  -- the final dimension-dependent exponent C
  set A : ℝ := ((n : ℝ) - 1) * a + (n : ℝ) * β with hA_def
  have hA_pos : 0 < A := by
    rw [hA_def]
    have hn2 : 2 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnR1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have ht1 : (0 : ℝ) < ((n : ℝ) - 1) * a := mul_pos hnR1 ha_pos
    have ht2 : (0 : ℝ) ≤ (n : ℝ) * β := mul_nonneg (by linarith) hβ_0
    linarith
  set C : ℝ := (G + A) / ε with hC_def
  have hCε : C * ε = A + G := by
    rw [hC_def]
    field_simp [hε.ne']
    ring
  have hNat1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred (by omega)
  have h_expRE : -G + -((n : ℝ) * β) = -(C * ε) + ((n - 1 : ℕ) : ℝ) * a := by
    rw [hNat1, hCε, hA_def]
    ring
  refine ⟨C, ?_, ?_⟩
  · rw [hC_def]
    exact div_pos (add_pos hG_pos hA_pos) hε
  · intro δ ρ hδ_pos hδ_le_ρ hρ_le_ρ0 hδ_lt ι s T hs hball hED
    have hρ_pos : 0 < ρ := lt_of_lt_of_le hδ_pos hδ_le_ρ
    have hδ_R_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hδ_R_nonneg : 0 ≤ (δ : ℝ) := hδ_R_pos.le
    have hρ_R_pos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ_pos
    have hρ_R_nonneg : 0 ≤ (ρ : ℝ) := hρ_R_pos.le
    have hρ_R_le_ρ₀ : (ρ : ℝ) ≤ (ρ₀ : ℝ) := by exact_mod_cast hρ_le_ρ0
    have hρ_le_1 : ρ ≤ 1 := le_trans hρ_le_ρ0 hρ₀1.le
    have hρ_R_le_1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ_le_1
    have hδ_le_ρC : (δ : ℝ) ≤ (ρ : ℝ) ^ C := hδ_lt.le
    have hρC_pos : 0 < (ρ : ℝ) ^ C := Real.rpow_pos_of_pos hρ_R_pos C
    have hρC_nonneg : 0 ≤ (ρ : ℝ) ^ C := hρC_pos.le
    -- the subpolynomial loss δ^(-ε) absorbs (ρ^C)^(-ε)
    have hδ_loss : (ρ : ℝ) ^ (-(C * ε)) ≤ (δ : ℝ) ^ (-ε) := by
      rw [show -(C * ε) = C * (-ε) by ring]
      rw [Real.rpow_mul hρ_R_nonneg C (-ε), Real.rpow_neg hρC_nonneg,
        Real.rpow_neg hδ_R_nonneg]
      exact inv_anti₀ (Real.rpow_pos_of_pos hδ_R_pos ε)
        (Real.rpow_le_rpow hδ_R_nonneg hδ_le_ρC hε.le)
    -- crude counting bound
    have m_pos : 0 < (s.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr hs)
    have m_nonneg : 0 ≤ (s.card : ℝ) := m_pos.le
    have h_card_le : (s.card : ℝ) ≤ D₀ * (1 / (ρ : ℝ)) ^ (2 * n) := by
      rw [hD₀_def]
      exact Tube.card_le_of_EssDistinct hρ_pos 1 s (fun i => (T i).toTube) hball hED
    have hα2 : (s.card : ℝ) ^ (β / 2) ≤ D₀ ^ (β / 2) * (ρ : ℝ) ^ (-((n : ℝ) * β)) := by
      calc
        (s.card : ℝ) ^ (β / 2) ≤ (D₀ * (1 / (ρ : ℝ)) ^ (2 * n)) ^ (β / 2) :=
          Real.rpow_le_rpow m_nonneg h_card_le hβ2_nn
        _ = D₀ ^ (β / 2) * ((1 / (ρ : ℝ)) ^ (2 * n)) ^ (β / 2) := by
          rw [Real.mul_rpow hD₀_pos.le (pow_nonneg (one_div_nonneg.mpr hρ_R_pos.le) (2 * n))]
        _ = D₀ ^ (β / 2) * (ρ : ℝ) ^ (-((n : ℝ) * β)) := by
          have hstep : ((1 / (ρ : ℝ)) ^ (2 * n)) ^ (β / 2) = (ρ : ℝ) ^ (-((n : ℝ) * β)) := by
            calc
              ((1 / (ρ : ℝ)) ^ (2 * n)) ^ (β / 2) =
                  (1 / (ρ : ℝ)) ^ (((2 * n : ℕ) : ℝ) * (β / 2)) := by
                rw [← Real.rpow_natCast (1 / (ρ : ℝ)) (2 * n),
                  Real.rpow_mul (one_div_nonneg.mpr hρ_R_pos.le) ((2 * n : ℕ) : ℝ) (β / 2)]
              _ = (1 / (ρ : ℝ)) ^ ((n : ℝ) * β) := by
                congr 1
                rw [Nat.cast_mul]
                norm_num
                ring
              _ = (ρ : ℝ) ^ (-((n : ℝ) * β)) := by
                rw [one_div, Real.inv_rpow hρ_R_nonneg, ← Real.rpow_neg hρ_R_nonneg]
          rw [hstep]
    -- D₀^(β/2) ≤ ρ^(-G)
    have hD₀G : D₀ ^ (β / 2) ≤ (ρ₀ : ℝ) ^ (-G) := by
      calc
        D₀ ^ (β / 2) = (ρ₀ : ℝ) ^ (-G₀) := hG₀_eq.symm
        _ ≤ (ρ₀ : ℝ) ^ (-G) := by
          exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hρ₀_R_pos hρ₀_R_lt).mpr
            (by linarith [hG₀_le_G])
    have hD₀ρ : D₀ ^ (β / 2) ≤ (ρ : ℝ) ^ (-G) := by
      calc
        D₀ ^ (β / 2) ≤ (ρ₀ : ℝ) ^ (-G) := hD₀G
        _ ≤ (ρ : ℝ) ^ (-G) := by
          rw [hrpow_inv (ρ₀ : ℝ) hρ₀_R_pos, hrpow_inv (ρ : ℝ) hρ_R_pos]
          exact Real.rpow_le_rpow (le_of_lt (one_div_pos.mpr hρ₀_R_pos))
            (one_div_le_one_div_of_le hρ_R_pos hρ_R_le_ρ₀) hG_pos.le
    -- main estimate chain
    have h_mα : (s.card : ℝ) ^ (β / 2) ≤
        (δ : ℝ) ^ (-ε) * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a) := by
      calc
        (s.card : ℝ) ^ (β / 2) ≤ D₀ ^ (β / 2) * (ρ : ℝ) ^ (-((n : ℝ) * β)) := hα2
        _ ≤ (ρ : ℝ) ^ (-G) * (ρ : ℝ) ^ (-((n : ℝ) * β)) :=
          mul_le_mul_of_nonneg_right hD₀ρ (Real.rpow_nonneg hρ_R_nonneg _)
        _ = (ρ : ℝ) ^ (-G + -((n : ℝ) * β)) := by rw [Real.rpow_add hρ_R_pos]
        _ = (ρ : ℝ) ^ (-(C * ε) + (((n - 1 : ℕ) : ℝ) * a)) := by rw [h_expRE]
        _ = (ρ : ℝ) ^ (-(C * ε)) * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a) := by
          rw [Real.rpow_add hρ_R_pos]
        _ ≤ (δ : ℝ) ^ (-ε) * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a) :=
          mul_le_mul_of_nonneg_right hδ_loss (Real.rpow_nonneg hρ_R_nonneg _)
    -- |s|^(β/2) · |s|^(1-β/2) = |s|, reassembled
    have hY_real : (s.card : ℝ) ≤
        (δ : ℝ) ^ (-ε) * ((s.card : ℝ) * (ρ : ℝ) ^ (n - 1)) ^ (1 - β / 2) := by
      have hY : (s.card : ℝ) ≤
          (δ : ℝ) ^ (-ε) * ((s.card : ℝ) * (ρ : ℝ) ^ (n - 1)) ^ a := by
        calc
          (s.card : ℝ) = (s.card : ℝ) ^ (β / 2) * (s.card : ℝ) ^ a := by
            rw [← Real.rpow_add m_pos, show β / 2 + a = 1 by rw [ha_def]; ring, Real.rpow_one]
          _ ≤ ((δ : ℝ) ^ (-ε) * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a)) * (s.card : ℝ) ^ a :=
            mul_le_mul_of_nonneg_right h_mα (Real.rpow_nonneg m_nonneg a)
          _ = (δ : ℝ) ^ (-ε) * ((s.card : ℝ) * (ρ : ℝ) ^ (n - 1)) ^ a := by
            calc
              ((δ : ℝ) ^ (-ε) * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a)) * (s.card : ℝ) ^ a
                  = (δ : ℝ) ^ (-ε) * ((s.card : ℝ) ^ a * (ρ : ℝ) ^ (((n - 1 : ℕ) : ℝ) * a)) := by
                    ring
              _ = (δ : ℝ) ^ (-ε) * ((s.card : ℝ) ^ a * ((ρ : ℝ) ^ ((n - 1 : ℕ) : ℝ)) ^ a) := by
                rw [Real.rpow_mul hρ_R_nonneg ((n - 1 : ℕ) : ℝ) a]
              _ = (δ : ℝ) ^ (-ε) * ((s.card : ℝ) ^ a * ((ρ : ℝ) ^ (n - 1)) ^ a) := by
                rw [Real.rpow_natCast (ρ : ℝ) (n - 1)]
              _ = (δ : ℝ) ^ (-ε) * (((s.card : ℝ) * (ρ : ℝ) ^ (n - 1)) ^ a) := by
                rw [Real.mul_rpow m_pos.le (pow_nonneg hρ_R_nonneg (n - 1))]
      simpa [ha_def] using hY
    -- transfer to ENNReal
    have h_ρpow_eq : (ρ : ENNReal) ^ (n - 1) = ENNReal.ofReal ((ρ : ℝ) ^ (n - 1)) := by
      rw [ENNReal.ofReal_pow hρ_R_pos.le, ENNReal.ofReal_coe_nnreal]
    have h_card_mul_pos : (0 : ℝ) < (s.card : ℝ) * (ρ : ℝ) ^ (n - 1) :=
      mul_pos m_pos (pow_pos hρ_R_pos (n - 1))
    have h_card_mul_eq : (s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1) =
        ENNReal.ofReal ((s.card : ℝ) * (ρ : ℝ) ^ (n - 1)) := by
      rw [show (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) from
            (ENNReal.ofReal_natCast _).symm]
      rw [h_ρpow_eq, ENNReal.ofReal_mul (Nat.cast_nonneg s.card)]
    have hN : (s.card : ENNReal) ≤ (δ : ENNReal) ^ (-ε) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1)) ^ (1 - β / 2) := by
      rw [h_card_mul_eq]
      rw [show (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) from
            (ENNReal.ofReal_natCast _).symm]
      rw [ennreal_coe_nnreal_rpow hδ_R_pos,
          ENNReal.ofReal_rpow_of_pos h_card_mul_pos,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_R_pos.le (-ε))]
      exact ENNReal.ofReal_le_ofReal hY_real
    -- Frostman constant and tube factors are ≥ 1
    set FC : ENNReal := ConvexSpaceBody.frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall with hFC_def
    have hFC1 : (1 : ENNReal) ≤ FC := by
      rw [hFC_def]
      apply one_le_frostmanConstIn
      rw [densityIn_pos_iff]
      rcases hs with ⟨i₀, hi₀⟩
      refine ⟨i₀, hi₀, ?_, ?_⟩
      · have hvol_lower_pos : (0 : ENNReal) <
          (Tube.le_volume.c n : ENNReal) * (ρ : ENNReal) ^ (n - 1) := by
          exact_mod_cast (mul_pos (Tube.le_volume.c_pos n) (pow_pos hρ_pos (n - 1)))
        have hvol : 0 < volume (T i₀).carrier :=
          lt_of_lt_of_le hvol_lower_pos (Tube.le_volume (T i₀).toTube)
        simpa using hvol
      · change (T i₀).toConvexSpaceBody.carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
        rw [ConvexSpaceBody.closedUnitBall_carrier]
        exact hball i₀ hi₀
    have hρ_pow : (1 : ENNReal) ≤ (ρ : ENNReal) ^ (-2 * β) := by
      rw [show -2 * β = -(2 * β) by ring]
      rw [ENNReal.rpow_neg]
      exact ENNReal.one_le_inv.mpr (ENNReal.rpow_le_one (by exact_mod_cast hρ_le_1) (by linarith))
    have hμN : multiplicity s (fun i ↦ (T i).toShadedBody) ≤ (s.card : ENNReal) :=
      ShadedBody.multiplicity_le_card s (fun i ↦ (T i).toShadedBody)
    exact mult_le_pad (a := a) (μ := multiplicity s (fun i ↦ (T i).toShadedBody))
      (N := (s.card : ENNReal)) (F := FC)
      (R := (ρ : ENNReal) ^ (-2 * β))
      (X := (s.card : ENNReal) * (ρ : ENNReal) ^ (n - 1))
      (D := (δ : ENNReal) ^ (-ε)) hFC1 hρ_pow ha_nn hμN hN

/-- **Blueprint `lem:genKFAuxScale` reduces to the uniform form of blueprint `genKF`.**

Let `ρ₀ < 1` and `η'` be a threshold and parameter for
`Kakeya.FrostmanEstimate.MultiplicityBoundUniform` at `ε`, let `C` be the exponent that
`Kakeya.FrostmanEstimate.multiplicity_le_of_deep_aux_scale` supplies for that `ρ₀`, and set
`η := η' / C`.  Split on the size of the tube scale `ρ`, in *three* regimes:

* *Bounded tube scale*, `ρ₀ ≤ ρ`: this is
  `Kakeya.FrostmanEstimate.multiplicity_le_of_bounded_tube_scale`, which needs no hypothesis
  beyond the geometry.
* *Deep auxiliary scale*, `ρ < ρ₀` and `δ < ρ ^ C`: this is
  `Kakeya.FrostmanEstimate.multiplicity_le_of_deep_aux_scale`, likewise unconditional.
* *Small tube scale*, `ρ < ρ₀` and `ρ ^ C ≤ δ`: apply the uniform bound at scale `ρ`.  Its
  fullness hypothesis is available because `λ ≥ δ ^ η = δ ^ (η'/C) ≥ (ρ ^ C) ^ (η'/C) = ρ ^ η'`,
  and its loss satisfies `ρ ^ (-ε) ≤ δ ^ (-ε)` since `δ ≤ ρ ≤ 1`.

The blueprint runs only the first and last of these, and obtains the fullness hypothesis of the
last from `λ ≥ δ ^ η` and `δ ≤ ρ ≤ 1` alone; that step is invalid, since `δ ≤ ρ` and `η > 0`
give `δ ^ η ≤ ρ ^ η`.  The middle regime and the rescaling `η := η' / C` are what repair it; see
`Kakeya.FrostmanEstimate.multiplicity_le_of_deep_aux_scale`.

The three regimes cover every `ρ ∈ [δ, 1]`, and no threshold depends on the family, hence none
depends on `C_F(𝕍, B₁)` — which is what makes the stated quantifier order attainable. -/
theorem FrostmanEstimate.multiplicity_bound_auxScale_of_uniform {β : ℝ} (hβ_0 : 0 ≤ β)
    (hβ_1 : β ≤ 1) (hn : 1 < Module.finrank ℝ E)
    (hU : FrostmanEstimate.MultiplicityBoundUniform.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (δ : ENNReal) ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η', hη'_pos, hev⟩ := hU ε hε
  let P : NNReal → Prop := fun ρ =>
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (ρ : ENNReal) ^ η' →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (ρ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2)
  -- a threshold ρ₀ < 1 below which the uniform bound's predicate holds
  have hev_lt1 : ∀ᶠ ρ in 𝓝[>] (0 : NNReal), P ρ ∧ ρ < 1 := by
    filter_upwards [hev, nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with ρ hρ hρ1
    exact ⟨hρ, hρ1⟩
  obtain ⟨ρ₀, hρ₀_Ioi, hIoc⟩ :=
    (mem_nhdsGT_iff_exists_Ioc_subset (a := (0 : NNReal))
      (s := {ρ : NNReal | P ρ ∧ ρ < 1})).mp hev_lt1
  have hρ₀_pos : 0 < ρ₀ := Set.mem_Ioi.mp hρ₀_Ioi
  have hρ₀_lt1 : ρ₀ < 1 := (hIoc ⟨hρ₀_pos, le_rfl⟩).2
  obtain ⟨C, hC_pos, hdeep⟩ :=
    multiplicity_le_of_deep_aux_scale E hβ_0 hβ_1 hn hε hρ₀_pos hρ₀_lt1
  refine ⟨η' / C, by positivity, ?_⟩
  filter_upwards
    [multiplicity_le_of_bounded_tube_scale E hβ_0 hβ_1 hn hε hρ₀_pos,
     self_mem_nhdsWithin]
    with δ hbdd hδ_pos
  intro ρ hδρ hρ1 ι s T hne hball hED hfull
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hδ_pos hδρ
  by_cases hbig : ρ₀ ≤ ρ
  · exact hbdd ρ hbig hρ1 s T hne hball hED
  push Not at hbig
  by_cases hdeepcase : (δ : ℝ) < (ρ : ℝ) ^ C
  · exact hdeep δ ρ hδ_pos hδρ hbig.le hdeepcase s T hne hball hED
  push Not at hdeepcase
  -- small tube scale: ρ < ρ₀ and (ρ : ℝ)^C ≤ (δ : ℝ)
  have hρ_pow_le : (ρ : ENNReal) ^ η' ≤ (δ : ENNReal) ^ (η' / C) := by
    have hδ_R_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hρ_R_pos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ_pos
    rw [ennreal_coe_nnreal_rpow hρ_R_pos, ennreal_coe_nnreal_rpow hδ_R_pos]
    apply ENNReal.ofReal_le_ofReal
    calc
      (ρ : ℝ) ^ η' = ((ρ : ℝ) ^ C) ^ (η' / C) := by
        rw [← Real.rpow_mul hρ_R_pos.le]
        congr 1
        field_simp [hC_pos.ne']
      _ ≤ (δ : ℝ) ^ (η' / C) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hρ_R_pos.le _) hdeepcase (by positivity)
  have hfull_ρ : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (ρ : ENNReal) ^ η' :=
    le_trans hρ_pow_le hfull
  have hsmall := (hIoc ⟨hρ_pos, hbig.le⟩).1 s T hne hball hED hfull_ρ
  have hρ_le_δ_neg : (ρ : ENNReal) ^ (-ε) ≤ (δ : ENNReal) ^ (-ε) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow (by exact_mod_cast hδρ) hε.le)
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (ρ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
      hsmall
    _ ≤ (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      gcongr

/-- **[GWZ, Lemma 3.9] with an auxiliary scale** (blueprint `lem:genKFAuxScale`).

This is `Kakeya.FrostmanEstimate.multiplicity_bound` with the smallness quantifier and the
subpolynomial loss moved off the tube scale `ρ` onto an *auxiliary* parameter `δ ≤ ρ`: the
family consists of `ρ`-tubes, but the fullness hypothesis and the loss are measured in `δ`.
Section 8 needs this form because the tube scale there is a rescaled scale such as `τ / δ`
or `θ / τ`, which need not be small, while `δ` always is.

Following GWZ, the Frostman constant `C_F(𝕍, B₁)` of the family is a *factor in the
conclusion* rather than a hypothesis, so that the smallness threshold for `δ` depends only on
`ε` and `β`; the order of quantifiers is the one of
`Kakeya.FrostmanEstimate.multiplicity_bound` and is essential, `η` depending only on `ε` and
`β`.  See `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn` for the
derived form taking a constant as a hypothesis.  The dimension hypothesis
`1 < Module.finrank ℝ E` is the blueprint's `n ≥ 2`.

**Nothing is open here: this theorem is proved.**  The chain is

* `Kakeya.FrostmanEstimate.multiplicity_bound` — GWZ Lemma 3.9 at a single scale, proved from
  the *rigid-motion* form of GWZ Lemma 3.8, `Kakeya.exists_randCF_rigid_family`;
* `Kakeya.FrostmanEstimate.multiplicityBoundUniform` — the same statement with the ball
  hypothesis relaxed from `∀ i` to `∀ i ∈ s`, by reindexing along `Finset.attach`;
* `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_uniform` — the auxiliary scale, by the
  three-regime split described there.

That record was
**stale**, and the way it was stale is worth keeping, since the same trap is easy to re-enter:
it described the obstruction of the *translation-only* route, which by then had been superseded.

The translation route (`Kakeya.exists_randCF_translation_family`) translates the family
`⌈C_F⌉₊` times and its ED-multiplicity cap is `J · C_pack = Ω(C_F)`.  That `Ω(C_F)` is
*geometric*, not an artifact: a parallel-packing family of `⌈C_F⌉₊` directions inside a
`δ ^ (1/2)`-cap forces multiplicity `≥ c_n · ⌈C_F⌉₊` for every admissible translation vector, so
no probabilistic refinement removes it, and `Kakeya.isEDUpToMult_translate_product_of_thinBox_pack`
is sharp in its `J`-dependence.  Since `Kakeya.FrostmanEstimate.ball2_version_edUpToMult` charges
the cap as a `δ ^ (-η)` loss, that route really does only reach `C_F ≤ δ ^ (-θ)`, which is what
`Kakeya.FrostmanEstimate.MultiplicityBoundUniformUpTo` and
`Kakeya.FrostmanEstimate.multiplicity_bound_uniform_upTo` record.

The rigid-motion route removes exactly that: its cap is `rigidMED C_EDlog δ = O(log (1/δ))`,
independent of the Frostman constant — see the header of
`Kakeya/RandomTranslation/RigidRandCFFinal.lean`, which says so and identifies the cap as the
replacement for `M_ED := ⌈C_F⌉₊ · C_pack_ext + 1`.  Once
`Kakeya.FrostmanEstimate.multiplicity_bound` was reproved from it, the range restriction was gone
and only the binder was left, but the docstring here was not revisited.  The two remaining
"differences" it listed are not differences at all:
`Kakeya.ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant` is `rfl`, and the quantifier order
of `multiplicity_bound` already places `C_F` in the conclusion, after the family — blueprint
`note:genKFConstantPlacement`.

So `Kakeya.FrostmanEstimate.MultiplicityBoundUniformUpTo` is now of historical interest only: it
is `MultiplicityBoundUniform` plus a hypothesis that is never needed.  It is kept because it is
the honest ceiling of the translation construction, and deleting it would erase the reason the
rigid construction exists.

One warning survives unchanged.  This theorem's statement must not be weakened to make anything
close: its shape is fixed by its consumers.  GWZ Lemma 6.4 applies it at a *rescaled* tube scale
with an unrestricted auxiliary scale, exactly as the Katz--Tao twin
`Kakeya.KatzTaoEstimate.plankEstimate` applies `Kakeya.exists_b0_multiplicity_bound` at plank
scale `b` with the auxiliary scale left free.  The `∀ ρ, δ ≤ ρ → ρ ≤ 1` binder and the
family-independence of `η` are both load bearing. -/
theorem FrostmanEstimate.multiplicity_bound_auxScale {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (δ : ENNReal) ^ η →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  exact FrostmanEstimate.multiplicity_bound_auxScale_of_uniform E hβ_0 hβ_1 hn
    (FrostmanEstimate.multiplicityBoundUniform E hβ_0 hβ_1 hn h)

/-- **[GWZ, Lemma 3.9] with an auxiliary scale, in constant-hypothesis form.**

The caller-facing shape of `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`: a bound
`C_F(𝕍, B₁) ≤ C` is supplied as the hypothesis that `𝕍` is `C`-Frostman in `B₁`, and `C`
appears in the conclusion in place of the Frostman constant itself.  The quantifier `∀ C`
sits *inside* the `∀ᶠ δ`, so `C` may depend on `δ`; Section 8 uses this at
`C = δ ^ (-a)` and `C = L · δ ^ (-n₀)`. -/
theorem FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn {β : ℝ} (hβ_0 : 0 ≤ β)
    (hβ_1 : β ≤ 1) (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
    ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube ρ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ (δ : ENNReal) ^ η →
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall C →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) * C ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := multiplicity_bound_auxScale E hβ_0 hβ_1 hn h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro C hC1 hCtop ρ hδρ hρ1 ι s T hne hball hED hfull hFrost
  have hfc_le : ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ C := frostmanConstIn_le hFrost
  have hnonneg : 0 ≤ 1 - β / 2 := by nlinarith [hβ_1]
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) *
        ConvexSpaceBody.frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall ^ (1 - β / 2) *
        (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) :=
      hδ ρ hδρ hρ1 s T hne hball hED hfull
    _ ≤ (δ : ENNReal) ^ (-ε) * C ^ (1 - β / 2) * (ρ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
      gcongr

/-- **[GWZ, Lemma 3.9], arbitrary-upper-bound form.** The stable entry point for Section 6.

Any admissible Frostman constant `CF` may be supplied *after* `δ` and the family are fixed; the
estimate follows from the canonical form by `frostmanConstant ≤ CF` and monotonicity of
`x ↦ x ^ (1 - β/2)`, whose exponent is nonnegative because `β ≤ 1 ≤ 2`.

The quantifier order is `∀ᶠ δ, ∀ family, ∀ CF` — never `∀ CF, ∀ᶠ δ`. -/
theorem FrostmanEstimate.multiplicity_bound_isFrostmanIn {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1)
    (hn : 1 < Module.finrank ℝ E) (h : FrostmanEstimate.{v} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∀ CF : ENNReal,
      IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall CF →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) *
        (δ : ENNReal) ^ (-2 * β) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ := FrostmanEstimate.multiplicity_bound (E := E) hβ_0 hβ_1 hn h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι s T hB hED hfull CF hCF
  refine (hδ s T hB hED hfull).trans ?_
  have h_frost_le :
      ConvexSpaceBody.frostmanConstant s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ CF :=
    ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hCF
  have h_exp_nonneg : 0 ≤ 1 - β / 2 := by linarith
  have hpow_le :
      (ConvexSpaceBody.frostmanConstant s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) ≤ CF ^ (1 - β / 2) :=
    ENNReal.rpow_le_rpow h_frost_le h_exp_nonneg
  gcongr


end FrostmanEstimate
end Kakeya
