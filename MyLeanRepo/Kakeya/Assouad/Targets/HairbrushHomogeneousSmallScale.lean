import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DirectionPacking2D
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AdditiveVolumeFromMultiplicity
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

/-!
# Constant-scale easy branch of the homogeneous hairbrush lemma

When the common angular scale is only a fixed multiple of the tube thickness,
direction-cap packing bounds pointwise multiplicity by a fixed constant.  The
incidence mass lower bound then closes the original-coordinate fiber target
without two-ends or a hairbrush.
-/

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open MeasureTheory

/-- Pointwise multiplicity bound for the small-scale case.

When all tube directions lie within `theta` of `v0` and `theta ≤ scaleSeparation * δ`,
direction-cap packing bounds the number of tubes through any point by a constant
depending only on `scaleSeparation`. -/
lemma small_scale_multiplicity_bound
    {δ theta scaleSeparation : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (htheta : δ ≤ theta) (htheta1 : theta ≤ 1)
    (hsmall : theta ≤ scaleSeparation * δ)
    (hscale : 1 ≤ scaleSeparation)
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (h_angle : HairbrushAngleSeparated F)
    (v0 : Point3) (hv0 : ‖v0‖ = 1)
    (hcap : ∀ T ∈ F, hairbrushAcuteDirectionAngle T.direction v0 ≤ theta)
    (C : ℕ) (hC : 300 * scaleSeparation ^ 2 ≤ (C : ℝ)) :
    ∀ x : Point3, shadedMultiplicity' Y x ≤ C := by
  intro x
  let through : Finset (Kakeya.DeltaTube δ) := F.filter fun T => x ∈ Y.carrier T
  let dirs : Finset Point3 := through.image fun T => T.direction
  have h_through_sub : through ⊆ F := Finset.filter_subset _ _
  have h1 : ∀ v ∈ dirs, ‖v‖ = 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, _, rfl⟩
    exact T.direction_unit
  have h2 : ∀ v ∈ dirs, ∀ w ∈ dirs, v ≠ w → (2 * δ / Real.pi) ≤ dist v w := by
    intro v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨U, hU, rfl⟩
    have hT_ne_U : T ≠ U := by
      intro h; rw [h] at hne; exact hne rfl
    have hT_F : T ∈ F := h_through_sub hT
    have hU_F : U ∈ F := h_through_sub hU
    have h_xT : x ∈ Y.carrier T := (Finset.mem_filter.mp hT).2
    have h_xU : x ∈ Y.carrier U := (Finset.mem_filter.mp hU).2
    have h_subT : Y.carrier T ⊆ T.carrier := Y.subset_tube hT_F
    have h_subU : Y.carrier U ⊆ U.carrier := Y.subset_tube hU_F
    have h_inter : T.carrier ∩ U.carrier ≠ ∅ := by
      exact Set.nonempty_iff_ne_empty.mp ⟨x, h_subT h_xT, h_subU h_xU⟩
    have h_ang : δ ≤ hairbrushAcuteAngle T U := h_angle T hT_F U hU_F hT_ne_U h_inter
    have h_dist : (2 / Real.pi) * hairbrushAcuteAngle T U ≤ dist T.direction U.direction :=
      acute_angle_dist_lower T.direction_unit U.direction_unit
    calc dist T.direction U.direction
      ≥ (2 / Real.pi) * hairbrushAcuteAngle T U := h_dist
    _ ≥ (2 / Real.pi) * δ := by gcongr
    _ = 2 * δ / Real.pi := by ring
  have h3 : ∀ v ∈ dirs, hairbrushAcuteDirectionAngle v v0 ≤ theta := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    exact hcap T (h_through_sub hT)
  have h4 : (dirs.card : ℝ) ≤ 300 * (theta / δ) ^ 2 :=
    direction_cap_packing_2d hδ hδ1 htheta htheta1 h1 h2 v0 hv0 h3
  have h_inj : Set.InjOn (fun T : Kakeya.DeltaTube δ => T.direction) (through : Set _) := by
    intro T hT U hU h_eq
    by_contra hne
    have hT_F : T ∈ F := h_through_sub hT
    have hU_F : U ∈ F := h_through_sub hU
    have h_xT : x ∈ Y.carrier T := (Finset.mem_filter.mp hT).2
    have h_xU : x ∈ Y.carrier U := (Finset.mem_filter.mp hU).2
    have h_subT : Y.carrier T ⊆ T.carrier := Y.subset_tube hT_F
    have h_subU : Y.carrier U ⊆ U.carrier := Y.subset_tube hU_F
    have h_inter : T.carrier ∩ U.carrier ≠ ∅ := by
      exact Set.nonempty_iff_ne_empty.mp ⟨x, h_subT h_xT, h_subU h_xU⟩
    have h_ang : δ ≤ hairbrushAcuteAngle T U := h_angle T hT_F U hU_F hne h_inter
    have h_dist : (2 / Real.pi) * hairbrushAcuteAngle T U ≤ dist T.direction U.direction :=
      acute_angle_dist_lower T.direction_unit U.direction_unit
    have h_pos : 0 < (2 / Real.pi) * δ := by positivity
    have h_lower : (2 / Real.pi) * δ ≤ dist T.direction U.direction := by
      calc (2 / Real.pi) * δ
        ≤ (2 / Real.pi) * hairbrushAcuteAngle T U := by gcongr
      _ ≤ dist T.direction U.direction := h_dist
    have h_cont : 0 < dist T.direction U.direction := h_pos.trans_le h_lower
    have h_eq2 : dist T.direction U.direction = 0 := by
      have h : T.direction = U.direction := h_eq
      simp [h]
    rw [h_eq2] at h_cont <;> linarith
  have h5 : through.card = dirs.card := by
    rw [← Finset.card_image_of_injOn h_inj] <;> rfl
  have h_ratio : theta / δ ≤ scaleSeparation := by
    have hδ_pos : 0 < δ := hδ
    calc theta / δ
      ≤ (scaleSeparation * δ) / δ := by gcongr
    _ = scaleSeparation := by
      field_simp [hδ_pos.ne'] <;> ring
  have h6 : (theta / δ) ^ 2 ≤ scaleSeparation ^ 2 := by
    have h_nonneg : 0 ≤ theta / δ := by
      apply div_nonneg
      · linarith
      · linarith
    gcongr
  have h7 : (through.card : ℝ) ≤ 300 * scaleSeparation ^ 2 := by
    rw [h5]
    have h : (dirs.card : ℝ) ≤ 300 * scaleSeparation ^ 2 := h4.trans (by gcongr)
    exact h
  have h8 : (through.card : ℝ) ≤ (C : ℝ) := h7.trans hC
  have h9 : shadedMultiplicity' Y x = through.card := by
    rfl
  rw [h9]
  exact_mod_cast h8

theorem hairbrush_homogeneous_small_scale :
    HairbrushHomogeneousSmallScaleStatement := by
  intro eta loss scaleSeparation heta hloss hscale
  let C : ℕ := Nat.ceil (300 * scaleSeparation ^ 2)
  have hC_def : (C : ℝ) = Nat.ceil (300 * scaleSeparation ^ 2) := by simp [C]
  have hC_bound : 300 * scaleSeparation ^ 2 ≤ (C : ℝ) := Nat.le_ceil _
  have hC_pos : 0 < C := by
    apply Nat.ceil_pos.mpr
    have h : 0 < 300 * scaleSeparation ^ 2 := by positivity
    linarith
  set c : ℝ := Real.sqrt scaleSeparation * (C : ℝ) with hc_def
  have hc_pos : 0 < c := by positivity
  have h_e_pos : 0 < loss - eta := by linarith
  rcases Kakeya.Assouad.Subunit.exists_delta₀_mul_pow_le_one c hc_pos (loss - eta) h_e_pos with
    ⟨delta₁, hdelta₁_pos, hdelta₁_le_one, h_ineq⟩
  let delta₀ : ℝ := min delta₁ (1 / 1000)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le : delta₀ ≤ 1 / 1000 := min_le_right _ _
  have hdelta₀_le_delta₁ : delta₀ ≤ delta₁ := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ theta hδ hδle hδtheta htheta1 hsmall F hF_nonempty h_angle h_confined Y h_dense
  rcases h_confined with ⟨v0, hv0, hv0_cap⟩
  have hδ1 : δ ≤ 1 := by linarith
  -- Multiplicity bound
  have h_mult : ∀ x : Point3, shadedMultiplicity' Y x ≤ C :=
    small_scale_multiplicity_bound hδ hδ1 hδtheta htheta1 hsmall hscale
      h_angle v0 hv0 hv0_cap C hC_bound
  -- Mass upper bound from bounded multiplicity
  have h_mass_le : Y.mass ≤ (C : ENNReal) * volume Y.union :=
    mass_le_C_mul_volume' Y C h_mult
  -- Tube volume lower bound
  have h_vol_lower : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    canonical_volume_lower hδ
  -- Aggregate density gives mass lower bound
  have h_dense' : (Kakeya.realRpowENN δ eta) * F.enncard * Kakeya.deltaTubeVolume δ ≤ Y.mass := h_dense
  have h101 : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ := h_vol_lower
  have h10 : (Kakeya.realRpowENN δ eta) * F.enncard * ENNReal.ofReal (δ ^ 2) ≤ Y.mass := by
    have h : (Kakeya.realRpowENN δ eta) * F.enncard * ENNReal.ofReal (δ ^ 2) ≤
        (Kakeya.realRpowENN δ eta) * F.enncard * Kakeya.deltaTubeVolume δ := by
      exact mul_le_mul_of_nonneg_left h101 (by positivity)
    exact le_trans h h_dense'
  have hδ2 : ENNReal.ofReal (δ ^ 2) = Kakeya.realRpowENN δ 2 := by
    simp [Kakeya.realRpowENN, Real.rpow_two]
  have h11 : (Kakeya.realRpowENN δ eta) * ENNReal.ofReal (δ ^ 2) = Kakeya.realRpowENN δ (2 + eta) := by
    rw [hδ2]
    have h := Kakeya.Assouad.Subunit.realRpowENN_mul (δ := δ) (a := eta) (b := 2) hδ
    have h_comm : eta + 2 = 2 + eta := by ring
    rw [h_comm] at h
    exact h
  have h_mass_ge : Kakeya.realRpowENN δ (2 + eta) * F.enncard ≤ Y.mass := by
    have h : (Kakeya.realRpowENN δ eta) * F.enncard * ENNReal.ofReal (δ ^ 2) =
        Kakeya.realRpowENN δ (2 + eta) * F.enncard := by
      rw [show (Kakeya.realRpowENN δ eta) * F.enncard * ENNReal.ofReal (δ ^ 2) =
          ((Kakeya.realRpowENN δ eta) * ENNReal.ofReal (δ ^ 2)) * F.enncard by ring]
      rw [h11] <;> ring
    rw [h] at h10
    exact h10
  -- Combine: lower bound ≤ mass ≤ C * volume
  have h12 : Kakeya.realRpowENN δ (2 + eta) * F.enncard ≤ (C : ENNReal) * volume Y.union :=
    le_trans h_mass_ge h_mass_le
  -- Asymptotic inequality
  have h13 : c * Real.rpow δ (loss - eta) ≤ 1 :=
    h_ineq δ hδ (le_trans hδle hdelta₀_le_delta₁)
  -- Fiber target
  by_cases hvol : volume Y.union = ⊤
  · simp only [HairbrushFiberTarget]
    rw [hvol]
    <;> exact le_top
  · have hF_card_pos : 0 < F.card := hF_nonempty.card_pos
    let N : ℝ := (F.card : ℝ)
    have hN_pos : 0 < N := by
      have h : (F.card : ℝ) > 0 := by exact_mod_cast hF_card_pos
      exact h
    have hN_one : 1 ≤ N := by
      have h : 1 ≤ F.card := by omega
      have h' : (1 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h
      exact h'
    have hF_eq : F.enncard = ENNReal.ofReal N := by
      simp [Kakeya.TubeFamily.enncard, N]
      <;> norm_cast
    set B : ENNReal :=
        Kakeya.realRpowENN δ (3 / 2 + loss) *
        ENNReal.ofReal (Real.sqrt theta) *
        ENNReal.rpow F.enncard (1 / 2) with hB_def
    have hF_enncard_ne_zero : F.enncard ≠ 0 := by
      have h : F.enncard = (F.card : ENNReal) := by rfl
      rw [h]
      simp [hF_card_pos.ne']
    have hF_enncard_ne_top : F.enncard ≠ ⊤ := by
      have h : F.enncard = (F.card : ENNReal) := by rfl
      rw [h]
      simp
    have hB_ne_top : B ≠ ⊤ := by
      simp only [hB_def]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hF_enncard_ne_top
    have hA_ne_top : (Kakeya.realRpowENN δ (2 + eta) * F.enncard) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hF_enncard_ne_top
    -- Real version of the key inequality
    have h14 : Real.rpow δ (3 / 2 + loss) * Real.sqrt theta * Real.sqrt N * (C : ℝ) ≤
               Real.rpow δ (2 + eta) * N := by
      have hsqrt_theta : Real.sqrt theta ≤ Real.sqrt scaleSeparation * Real.sqrt δ := by
        have h1 : theta ≤ scaleSeparation * δ := hsmall
        have h2 : Real.sqrt theta ≤ Real.sqrt (scaleSeparation * δ) := Real.sqrt_le_sqrt h1
        have h3 : Real.sqrt (scaleSeparation * δ) = Real.sqrt scaleSeparation * Real.sqrt δ := by
          rw [Real.sqrt_mul] <;> linarith
        rw [h3] at h2 <;> exact h2
      have hsqrt_delta : Real.sqrt δ = Real.rpow δ (1 / 2) := by
        simp [Real.sqrt_eq_rpow]
      have h4 : Real.rpow δ (3 / 2 + loss) * Real.sqrt δ = Real.rpow δ (2 + loss) := by
        rw [hsqrt_delta]
        have h_sum : (3 / 2 + loss) + (1 / 2 : ℝ) = 2 + loss := by ring
        have h := Real.rpow_add hδ (3 / 2 + loss) (1 / 2 : ℝ)
        rw [h_sum] at h
        exact h.symm
      have h5 : Real.rpow δ (2 + loss) = Real.rpow δ (2 + eta) * Real.rpow δ (loss - eta) := by
        have h_sum : (2 + eta) + (loss - eta) = 2 + loss := by ring
        have h := Real.rpow_add hδ (2 + eta) (loss - eta)
        rw [h_sum] at h
        exact h
      have h_pos_rpow : 0 ≤ Real.rpow δ (2 + eta) := Real.rpow_nonneg (by linarith) _
      have h_pos_rpow2 : 0 ≤ Real.rpow δ (3 / 2 + loss) := Real.rpow_nonneg (by linarith) _
      calc
        Real.rpow δ (3 / 2 + loss) * Real.sqrt theta * Real.sqrt N * (C : ℝ)
          ≤ Real.rpow δ (3 / 2 + loss) * (Real.sqrt scaleSeparation * Real.sqrt δ) * Real.sqrt N * (C : ℝ) := by
            gcongr <;> exact h_pos_rpow2
        _ = Real.rpow δ (2 + loss) * Real.sqrt scaleSeparation * Real.sqrt N * (C : ℝ) := by
            rw [show Real.rpow δ (3 / 2 + loss) * (Real.sqrt scaleSeparation * Real.sqrt δ) =
                    Real.sqrt scaleSeparation * (Real.rpow δ (3 / 2 + loss) * Real.sqrt δ) by ring]
            rw [h4] <;> ring
        _ = Real.rpow δ (2 + eta) * (Real.rpow δ (loss - eta) * Real.sqrt scaleSeparation * (C : ℝ)) * Real.sqrt N := by
            rw [h5] <;> ring
        _ ≤ Real.rpow δ (2 + eta) * 1 * Real.sqrt N := by
            have h6 : Real.rpow δ (loss - eta) * Real.sqrt scaleSeparation * (C : ℝ) ≤ 1 := by
              have h7 : Real.rpow δ (loss - eta) * Real.sqrt scaleSeparation * (C : ℝ) = c * Real.rpow δ (loss - eta) := by
                simp [hc_def] <;> ring
              rw [h7] <;> exact h13
            gcongr <;> exact h_pos_rpow
        _ = Real.rpow δ (2 + eta) * Real.sqrt N := by ring
        _ ≤ Real.rpow δ (2 + eta) * N := by
            have h8 : Real.sqrt N ≤ N := by
              have h9 : 1 ≤ N := hN_one
              have h10 : Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
              have h11 : Real.sqrt (N ^ 2) = N := by
                rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg (by linarith)]
              rw [h11] at h10 <;> exact h10
            gcongr <;> exact h_pos_rpow
    -- Transfer to ENNReal
    have h15 : B.toReal * (C : ℝ) ≤ (Kakeya.realRpowENN δ (2 + eta) * F.enncard).toReal := by
      have hB_toReal : B.toReal = Real.rpow δ (3 / 2 + loss) * Real.sqrt theta * Real.sqrt N := by
        have h1 : B.toReal = (Kakeya.realRpowENN δ (3 / 2 + loss)).toReal *
            (ENNReal.ofReal (Real.sqrt theta)).toReal * (ENNReal.rpow F.enncard (1 / 2)).toReal := by
          simp [hB_def, ENNReal.toReal_mul] <;> ring
        rw [h1]
        have h2 : (Kakeya.realRpowENN δ (3 / 2 + loss)).toReal = Real.rpow δ (3 / 2 + loss) :=
          Kakeya.Assouad.Subunit.realRpowENN_toReal hδ
        have h3 : (ENNReal.ofReal (Real.sqrt theta)).toReal = Real.sqrt theta := by
          rw [ENNReal.toReal_ofReal (by positivity)]
        have h4 : (ENNReal.rpow F.enncard (1 / 2)).toReal = (F.enncard.toReal) ^ (1 / 2 : ℝ) :=
          (ENNReal.toReal_rpow F.enncard (1 / 2 : ℝ)).symm
        have h5 : F.enncard.toReal = N := by
          simp [Kakeya.TubeFamily.enncard, N] <;> norm_cast
        rw [h2, h3, h4, h5]
        have h6 : Real.sqrt N = N ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h6] <;> ring
      have hA_toReal : (Kakeya.realRpowENN δ (2 + eta) * F.enncard).toReal = Real.rpow δ (2 + eta) * N := by
        have h1 : (Kakeya.realRpowENN δ (2 + eta) * F.enncard).toReal =
            (Kakeya.realRpowENN δ (2 + eta)).toReal * F.enncard.toReal := ENNReal.toReal_mul
        rw [h1]
        have h2 : (Kakeya.realRpowENN δ (2 + eta)).toReal = Real.rpow δ (2 + eta) :=
          Kakeya.Assouad.Subunit.realRpowENN_toReal hδ
        have h3 : F.enncard.toReal = N := by
          simp [Kakeya.TubeFamily.enncard, N]
          <;> norm_cast
        rw [h2, h3] <;> ring
      rw [hB_toReal, hA_toReal]
      exact h14
    have hC_top : (C : ENNReal) * volume Y.union ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp
      · exact hvol
    have h16 : (Kakeya.realRpowENN δ (2 + eta) * F.enncard).toReal ≤ (C : ℝ) * (volume Y.union).toReal := by
      have h16' : (Kakeya.realRpowENN δ (2 + eta) * F.enncard).toReal ≤ ((C : ENNReal) * volume Y.union).toReal :=
        (ENNReal.toReal_le_toReal hA_ne_top hC_top).mpr h12
      have h17' : ((C : ENNReal) * volume Y.union).toReal = (C : ℝ) * (volume Y.union).toReal := by
        rw [ENNReal.toReal_mul] <;> norm_cast
      rw [h17'] at h16'
      exact h16'
    have h17 : B.toReal * (C : ℝ) ≤ (C : ℝ) * (volume Y.union).toReal := by
      linarith
    have hC_real_pos : 0 < (C : ℝ) := by exact_mod_cast hC_pos
    have h18 : B.toReal ≤ (volume Y.union).toReal := by
      nlinarith
    have h_final : B ≤ volume Y.union :=
      (ENNReal.toReal_le_toReal hB_ne_top hvol).mp h18
    simpa [HairbrushFiberTarget, hB_def] using h_final

end Kakeya.Assouad
