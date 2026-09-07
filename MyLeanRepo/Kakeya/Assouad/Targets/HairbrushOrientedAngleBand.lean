import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.OrientationInfrastructure
import MyLeanRepo.Kakeya.Assouad.Hairbrush.AcuteAngleHelpers
import MyLeanRepo.Kakeya.Assouad.Hairbrush.LogLossAbsorption
import MyLeanRepo.Kakeya.Assouad.Hairbrush.DyadicBandPigeonhole

/-!
# Oriented acute angle-band pigeonhole

Pigeonhole one dyadic acute-angle band from a supplied brush, then orient the
selected tubes toward the supplied stem.  This is the logarithmic band step
between (B.24) and (B.25).

Reuse `orientTube` and its carrier/cardinality lemmas.  Do not use the old
`HairbrushMultiplicityDenseTwoEndsCoreData`, run two-ends, or invoke Córdoba.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

theorem hairbrush_oriented_angle_band :
    HairbrushOrientedAngleBandStatement := by
  intro angleExponent bandLoss hangleExponent hbandLoss
  rcases hairbrush_log_poly_bound angleExponent bandLoss hangleExponent hbandLoss with
    ⟨delta₀, hdelta₀_pos, hdelta₀_le, h_log_bound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ hδ hδle angleScale hangleScale_pos hangleScale_lower hangleScale_le_one
    B Z hB_nonempty hB_ed stem h_angle h_inter
  have hδ_le_one : δ ≤ 1 := by linarith [hδle]
  have hangleScale_ge_dpow : δ ^ angleExponent ≤ angleScale := by
    have h1 : realRpowENN δ angleExponent = ENNReal.ofReal (δ ^ angleExponent) := by
      simp [realRpowENN] <;> rfl
    rw [h1] at hangleScale_lower
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hangleScale_lower
  set K : ℕ := Nat.ceil (Real.log (1 / angleScale) / Real.log 2) with hK_def
  set K' : ℕ := Nat.ceil (Real.log (1 / δ ^ angleExponent) / Real.log 2) with hK'_def
  have hK_le_K' : K ≤ K' := by
    have h1 : 1 / angleScale ≤ 1 / (δ ^ angleExponent) := by gcongr
    have h2 : Real.log (1 / angleScale) ≤ Real.log (1 / (δ ^ angleExponent)) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (1 / angleScale) / Real.log 2 ≤
        Real.log (1 / (δ ^ angleExponent)) / Real.log 2 := by gcongr
    rw [hK_def, hK'_def]
    exact Nat.ceil_mono h3
  have h_loss : (K : ℝ) + 1 ≤ Real.rpow δ (-bandLoss) := by
    have h1 : (K' : ℝ) + 2 ≤ Real.rpow δ (-bandLoss) := h_log_bound δ hδ hδle
    have h2 : (K : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hK_le_K'
    linarith
  rcases dyadic_angle_band_pigeonhole stem angleScale hangleScale_pos hangleScale_le_one
      hB_nonempty h_angle K rfl with
    ⟨k, hk_le, hband_nonempty, hcard_ge⟩
  set σ : ℕ → ℝ := fun j => if j < K then (2 : ℝ)^j * angleScale else 1 with hσ_def
  set source : Kakeya.TubeFamily δ :=
    B.filter (fun U => σ k ≤ hairbrushAcuteAngle stem U ∧
      hairbrushAcuteAngle stem U ≤ 2 * σ k) with hsource_def
  set sigma' : ℝ := σ k with hsigma'_def
  have hsource_sub : source ⊆ B := by
    simp [hsource_def] <;> exact Finset.filter_subset _ _
  have hsource_nonempty : source.Nonempty := hband_nonempty
  have hsource_angle : ∀ U ∈ source,
      sigma' ≤ hairbrushAcuteAngle stem U ∧ hairbrushAcuteAngle stem U ≤ 2 * sigma' := by
    intro U hU
    simp only [hsource_def, Finset.mem_filter] at hU
    exact hU.2
  have hsource_intersects : ∀ U ∈ source, (stem.carrier ∩ U.carrier).Nonempty := by
    intro U hU
    exact h_inter U (hsource_sub hU)
  have hangleScale_le_sigma : angleScale ≤ sigma' := by
    by_cases h : k < K
    · have hσ : sigma' = (2 : ℝ)^k * angleScale := by
        simp [hsigma'_def, hσ_def, h]
      rw [hσ]
      have h1 : (1 : ℝ) ≤ (2 : ℝ)^k := by
        have h2 : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
          intro n; induction n with
          | zero => norm_num
          | succ n ih => simp [pow_succ] at * <;> nlinarith
        exact h2 k
      nlinarith
    · have hk_eq_K : k = K := by omega
      have hσ : sigma' = 1 := by
        simp [hsigma'_def, hσ_def, hk_eq_K] <;> omega
      rw [hσ]
      exact hangleScale_le_one
  have hsigma_le_one : sigma' ≤ 1 := by
    by_cases h : k < K
    · have hσ : sigma' = (2 : ℝ)^k * angleScale := by
        simp [hsigma'_def, hσ_def, h]
      rw [hσ]
      have hK_pos : 0 < K := by omega
      have hK_nonneg : 0 ≤ Real.log (1 / angleScale) / Real.log 2 := by
        have h1 : 1 / angleScale ≥ 1 := by apply one_le_one_div <;> linarith
        have h2 : 0 ≤ Real.log (1 / angleScale) := Real.log_nonneg h1
        have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        exact div_nonneg h2 h3.le
      have h_lt_x : ((K - 1 : ℕ) : ℝ) < Real.log (1 / angleScale) / Real.log 2 := by
        have h1 : (K : ℝ) < Real.log (1 / angleScale) / Real.log 2 + 1 :=
          Nat.ceil_lt_add_one hK_nonneg
        have h2 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
          simp [Nat.cast_sub (show 0 < K from by omega)] <;> norm_num
        rw [h2] <;> linarith
      have h_k_le : (k : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      have h_k_lt_x : (k : ℝ) < Real.log (1 / angleScale) / Real.log 2 := by linarith
      set x : ℝ := Real.log (1 / angleScale) / Real.log 2 with hx_def
      have h_pow_k : (2 : ℝ)^k < (2 : ℝ)^x := by
        have h_cast : (2 : ℝ)^((k : ℝ)) = (2 : ℝ)^k := by rw [Real.rpow_natCast]
        have h_goal : (2 : ℝ)^((k : ℝ)) < (2 : ℝ)^x :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_k_lt_x
        rw [h_cast] at h_goal
        exact h_goal
      have h_eq_x : (2 : ℝ)^x = 1 / angleScale := by
        have h_pos : 0 < 1 / angleScale := by positivity
        have h : (2 : ℝ)^x = Real.exp (x * Real.log 2) := by
          rw [Real.rpow_def_of_pos (by norm_num)]
          rw [mul_comm (Real.log 2) x]
        rw [h]
        have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h2 : x * Real.log 2 = Real.log (1 / angleScale) := by
          simp only [hx_def]
          field_simp [hlog2_pos.ne']
        rw [h2, Real.exp_log h_pos]
      have h : (2 : ℝ)^k * angleScale < 1 := by
        calc (2 : ℝ)^k * angleScale
          < (2 : ℝ)^x * angleScale := by gcongr
        _ = (1 / angleScale) * angleScale := by rw [h_eq_x]
        _ = 1 := by field_simp [hangleScale_pos.ne'] <;> ring
      exact h.le
    · have hk_eq_K : k = K := by omega
      have hσ : sigma' = 1 := by
        simp [hsigma'_def, hσ_def, hk_eq_K] <;> omega
      rw [hσ] <;> norm_num
  -- Loss absorption: (K+1) * δ^bandLoss ≤ 1, so δ^bandLoss * B ≤ source
  have h1 : 0 < δ ^ bandLoss := by positivity
  have h2 : ((K : ℝ) + 1) * δ ^ bandLoss ≤ 1 := by
    have h3 : (K : ℝ) + 1 ≤ δ ^ (-bandLoss) := h_loss
    have h4 : δ ^ (-bandLoss) = 1 / δ ^ bandLoss := by
      rw [Real.rpow_neg hδ.le] <;> field_simp
    rw [h4] at h3
    have h5 : ((K : ℝ) + 1) * δ ^ bandLoss ≤ (1 / δ ^ bandLoss) * δ ^ bandLoss := by gcongr
    have h6 : (1 / δ ^ bandLoss) * δ ^ bandLoss = 1 := by field_simp [h1.ne']
    rw [h6] at h5
    exact h5
  have h3 : ((K : ℝ) + 1) ≥ 0 := by positivity
  have h4 : (K + 1 : ENNReal) * realRpowENN δ bandLoss ≤ 1 := by
    have h_eq1 : (K + 1 : ENNReal) = ENNReal.ofReal ((K : ℝ) + 1) := by norm_cast
    have h_eq2 : realRpowENN δ bandLoss = ENNReal.ofReal (δ ^ bandLoss) := by
      simp [realRpowENN] <;> rfl
    rw [h_eq1, h_eq2]
    have h_mul : ENNReal.ofReal ((K : ℝ) + 1) * ENNReal.ofReal (δ ^ bandLoss) =
             ENNReal.ofReal (((K : ℝ) + 1) * δ ^ bandLoss) := by
      have h9 : ENNReal.ofReal (((K : ℝ) + 1) * δ ^ bandLoss) =
               ENNReal.ofReal ((K : ℝ) + 1) * ENNReal.ofReal (δ ^ bandLoss) :=
        ENNReal.ofReal_mul h3
      exact h9.symm
    rw [h_mul]
    rw [ENNReal.ofReal_le_one] <;> linarith
  have h_retention : realRpowENN δ bandLoss * B.enncard ≤ source.enncard := by
    have h5 : B.enncard ≤ (K + 1 : ENNReal) * source.enncard := hcard_ge
    calc
      realRpowENN δ bandLoss * B.enncard
        ≤ realRpowENN δ bandLoss * ((K + 1 : ENNReal) * source.enncard) := by gcongr
      _ = (K + 1 : ENNReal) * realRpowENN δ bandLoss * source.enncard := by
        rw [mul_assoc, mul_comm (K + 1 : ENNReal)] <;> ring
      _ ≤ 1 * source.enncard := by gcongr
      _ = source.enncard := by simp
  have h_inj : Set.InjOn (orientTube stem) source :=
    orientTube_injOn hδ hδ_le_one hB_ed hsource_sub stem
  let oriented : Kakeya.TubeFamily δ := source.image (orientTube stem)
  have horiented_eq : oriented = source.image (orientTube stem) := rfl
  have horiented_card : oriented.enncard = source.enncard := by
    have h : oriented.card = source.card := Finset.card_image_of_injOn h_inj
    simp [Kakeya.TubeFamily.enncard, h]
  let shading' : Kakeya.Shading oriented := transportedShading Z stem hsource_sub
  have hshading_carrier : ∀ U ∈ source,
      shading'.carrier (orientTube stem U) = Z.carrier U := by
    intro U hU
    exact transportedShading_carrier Z stem hsource_sub h_inj hU
  have horiented_angle : ∀ U' ∈ oriented,
      sigma' ≤ Kakeya.Hairbrush.angleBetween stem U' ∧
        Kakeya.Hairbrush.angleBetween stem U' ≤ 2 * sigma' := by
    intro U' hU'
    rcases Finset.mem_image.mp hU' with ⟨U, hU, rfl⟩
    have h_angle' : Kakeya.Hairbrush.angleBetween stem (orientTube stem U) =
        hairbrushAcuteAngle stem U := orientTube_angle stem U
    rw [h_angle']
    exact hsource_angle U hU
  have horiented_intersects : ∀ U' ∈ oriented, (stem.carrier ∩ U'.carrier).Nonempty := by
    intro U' hU'
    rcases Finset.mem_image.mp hU' with ⟨U, hU, rfl⟩
    have hcar : (orientTube stem U).carrier = U.carrier := orientTube_carrier stem U
    rw [hcar]
    exact hsource_intersects U hU
  exact ⟨sigma', hangleScale_le_sigma, hsigma_le_one, source, hsource_sub,
    hsource_nonempty, h_retention, hsource_angle, hsource_intersects,
    oriented, horiented_eq, horiented_card, shading', hshading_carrier,
    horiented_angle, horiented_intersects⟩

end Kakeya.Assouad
