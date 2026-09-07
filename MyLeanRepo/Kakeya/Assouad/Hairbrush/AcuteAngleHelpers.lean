import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushTwoBroadLeaves
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Acute robust transversality helper lemmas
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

lemma hairbrushAcuteDirectionAngle_le_pi2 (v w : Point3) :
    hairbrushAcuteDirectionAngle v w ≤ Real.pi / 2 := by
  by_cases h : Real.arccos (inner ℝ v w) ≤ Real.pi / 2
  · exact min_le_iff.mpr (Or.inl h)
  · have h' : Real.pi - Real.arccos (inner ℝ v w) ≤ Real.pi / 2 := by linarith
    exact min_le_iff.mpr (Or.inr h')

lemma hairbrushAcuteDirectionAngle_self {v : Point3} (hv : ‖v‖ = 1) :
    hairbrushAcuteDirectionAngle v v = 0 := by
  have h1 : inner ℝ v v = 1 := by
    have h2 : inner ℝ v v = ‖v‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    rw [h2, hv] <;> norm_num
  dsimp only [hairbrushAcuteDirectionAngle]
  rw [h1]
  have h3 : Real.arccos (1 : ℝ) = 0 := Real.arccos_one
  rw [h3]
  have h4 : (0 : ℝ) ≤ Real.pi := by positivity
  rw [min_eq_left] <;> linarith

lemma hairbrushAcuteAngle_le_pi2 {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    hairbrushAcuteAngle T U ≤ Real.pi / 2 :=
  hairbrushAcuteDirectionAngle_le_pi2 T.direction U.direction

lemma hairbrushAcuteAngle_self {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    hairbrushAcuteAngle T T = 0 :=
  hairbrushAcuteDirectionAngle_self T.direction_unit

lemma hairbrushAcuteAngle_symm' {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    hairbrushAcuteAngle T U = hairbrushAcuteAngle U T := by
  have h : inner ℝ T.direction U.direction = inner ℝ U.direction T.direction :=
    real_inner_comm U.direction T.direction
  simp [hairbrushAcuteAngle, hairbrushAcuteDirectionAngle, h]

lemma hairbrushRobustQ_lt_one {δ aCore eta : ℝ}
    (hδ : 0 < δ) (hδ1000 : δ ≤ 1 / 1000) (haCore : 0 < aCore) (heta : 0 < eta) :
    hairbrushRobustQ δ aCore eta < 1 := by
  have h3 : 0 < δ ^ aCore := by positivity
  have h4 : δ ^ aCore < 1 := by
    have h5 : δ ^ aCore < 1 ^ aCore := by gcongr <;> linarith
    simpa using h5
  have h7 : 0 < δ ^ aCore / 8 := by positivity
  have h8 : δ ^ aCore / 8 < 1 := by
    have h81 : δ ^ aCore / 8 < δ ^ aCore := by
      have h82 : 0 < δ ^ aCore := h3
      nlinarith
    linarith [h4, h81]
  have h9 : 0 < 1 / eta := by positivity
  have h10 : (δ ^ aCore / 8) ^ (1 / eta) < 1 := by
    exact Real.rpow_lt_one (by linarith) h8 h9
  simpa [hairbrushRobustQ] using h10

lemma hairbrushRobustQ_pow_eta {δ aCore eta : ℝ}
    (hδ : 0 < δ) (haCore : 0 < aCore) (heta : 0 < eta) :
    (hairbrushRobustQ δ aCore eta) ^ eta = δ ^ aCore / 8 := by
  have hpos : 0 < δ ^ aCore / 8 := by positivity
  have h : (hairbrushRobustQ δ aCore eta) ^ eta =
      ((δ ^ aCore / 8) ^ (1 / eta)) ^ eta := by
    simp [hairbrushRobustQ]
  rw [h]
  have h2 : ((δ ^ aCore / 8) ^ (1 / eta)) ^ eta = (δ ^ aCore / 8) ^ ((1 / eta) * eta) := by
    rw [← Real.rpow_mul (by linarith)] <;> ring
  rw [h2]
  have h3 : (1 / eta) * eta = 1 := by field_simp [heta.ne'] <;> ring
  rw [h3] <;> simp

lemma near_set_small
    {δ theta eta aCore zetaEnds bTube : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (hAngleSep : HairbrushAngleSeparated F)
    (hTwoBroad : IsTwoBroadAtScale Y theta eta)
    (hδ : 0 < δ) (hδ1000 : δ ≤ 1 / 1000)
    (haCore : 0 < aCore) (heta : 0 < eta)
    (theta_pos : 0 < theta)
    (x : Point3) (hx : x ∈ core.Z.union)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ core.F3) (hxT : x ∈ core.Z.carrier T)
    (r : ℝ) (hr_def : r = max δ (hairbrushRobustQ δ aCore eta * theta / 4))
    (hM2 : 2 ≤ Nat.ceil (core.alphaMu * (core.mu : ℝ))) :
    let through_Z := core.F3.filter (fun U => x ∈ core.Z.carrier U)
    let near_Z := through_Z.filter (fun U => hairbrushAcuteAngle T U < r)
    (near_Z.card : ℝ) ≤ (through_Z.card : ℝ) / 2 := by
  let through_Z := core.F3.filter (fun U => x ∈ core.Z.carrier U)
  let near_Z := through_Z.filter (fun U => hairbrushAcuteAngle T U < r)
  have hT_in_through : T ∈ through_Z := by
    simp only [through_Z, Finset.mem_filter] <;> exact ⟨hT, hxT⟩
  have hthrough_ge2 : 2 ≤ through_Z.card := by
    have h1 : Nat.ceil (core.alphaMu * (core.mu : ℝ)) ≤ through_Z.card :=
      core.multiplicity_lower x hx
    exact hM2.trans h1
  by_cases h_case : hairbrushRobustQ δ aCore eta * theta / 4 ≤ δ
  · have hr_eq : r = δ := by
      rw [hr_def, max_eq_left h_case]
    have h_near_only_T : near_Z = {T} := by
      apply Finset.ext
      intro U
      simp only [near_Z, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hU_in_through, h_angle⟩
        have hU : U ∈ core.F3 := (Finset.mem_filter.mp hU_in_through).1
        have hxU : x ∈ core.Z.carrier U := (Finset.mem_filter.mp hU_in_through).2
        by_cases hne : U ≠ T
        · have hxT' : x ∈ T.carrier := Y.subset_tube (core.F3_subset hT) (core.Z_subset_Y T hT hxT)
          have hxU' : x ∈ U.carrier := Y.subset_tube (core.F3_subset hU) (core.Z_subset_Y U hU hxU)
          have h_inter : T.carrier ∩ U.carrier ≠ ∅ := by
            have h_nonempty : Set.Nonempty (T.carrier ∩ U.carrier) := ⟨x, hxT', hxU'⟩
            exact Set.nonempty_iff_ne_empty.mp h_nonempty
          have h_angle_sep : δ ≤ hairbrushAcuteAngle T U :=
            hAngleSep T (core.F3_subset hT) U (core.F3_subset hU) hne.symm h_inter
          rw [hr_eq] at h_angle
          linarith
        · have h_eq : U = T := by simpa using hne
          exact h_eq
      · intro h_eq
        rw [h_eq]
        have h5 : T ∈ through_Z := hT_in_through
        have h6 : hairbrushAcuteAngle T T < r := by
          rw [hairbrushAcuteAngle_self T, hr_eq] <;> linarith
        exact ⟨h5, h6⟩
    have h_main : (near_Z.card : ℝ) ≤ (through_Z.card : ℝ) / 2 := by
      rw [h_near_only_T]
      have h7 : (1 : ℝ) ≤ (through_Z.card : ℝ) / 2 := by
        have h8 : (2 : ℝ) ≤ (through_Z.card : ℝ) := by exact_mod_cast hthrough_ge2
        linarith
      simpa using h7
    exact h_main
  · have hq_pos : 0 < hairbrushRobustQ δ aCore eta := by
      dsimp only [hairbrushRobustQ]
      have h_base : 0 < δ ^ aCore / 8 := by positivity
      exact Real.rpow_pos_of_pos h_base _
    have hr_eq : r = hairbrushRobustQ δ aCore eta * theta / 4 := by
      rw [hr_def, max_eq_right (by linarith)]
    have hq_lt_one : hairbrushRobustQ δ aCore eta < 1 :=
      hairbrushRobustQ_lt_one hδ hδ1000 haCore heta
    have hxY : x ∈ Y.union := by
      have h2 : core.Z.union ⊆ Y.union := by
        intro y hy
        rcases hy with ⟨U, hU, hyU⟩
        exact ⟨U, core.F3_subset hU, core.Z_subset_Y U hU hyU⟩
      exact h2 hx
    rcases hTwoBroad x hxY with ⟨thetaLocal, hδ_le_tl, htheta_half_le_tl, htl_le_theta, h_broad⟩
    have hr_le_tl : r ≤ thetaLocal := by
      rw [hr_eq]
      have h1 : hairbrushRobustQ δ aCore eta * theta / 4 ≤ theta / 2 := by
        have h2 : hairbrushRobustQ δ aCore eta < 1 := hq_lt_one
        have h3 : hairbrushRobustQ δ aCore eta * theta / 4 < theta / 2 := by
          calc hairbrushRobustQ δ aCore eta * theta / 4
            < 1 * theta / 4 := by gcongr
          _ = theta / 4 := by ring
          _ ≤ theta / 2 := by linarith
        exact h3.le
      linarith
    let through_F := F.filter (fun U => x ∈ Y.carrier U)
    let near_F := through_F.filter (fun U => hairbrushAcuteDirectionAngle U.direction T.direction ≤ r)
    have h4' : (near_F.card : ℝ) ≤ (r / thetaLocal) ^ eta * (through_F.card : ℝ) := by
      simpa [through_F, near_F] using h_broad T.direction T.direction_unit r (by linarith) hr_le_tl
    have h5 : r / thetaLocal ≤ hairbrushRobustQ δ aCore eta / 2 := by
      rw [hr_eq]
      have h6 : thetaLocal ≥ theta / 2 := htheta_half_le_tl
      have h7 : hairbrushRobustQ δ aCore eta * theta / 4 / thetaLocal ≤
               hairbrushRobustQ δ aCore eta * theta / 4 / (theta / 2) := by gcongr
      have h8 : hairbrushRobustQ δ aCore eta * theta / 4 / (theta / 2) =
               hairbrushRobustQ δ aCore eta / 2 := by
        field_simp [theta_pos.ne'] <;> ring
      rw [h8] at h7
      exact h7
    have h5' : 0 ≤ r / thetaLocal := by
      have hr_pos' : 0 < r := by linarith [hr_eq, hq_pos, theta_pos]
      have htl_pos : 0 < thetaLocal := by linarith [hδ_le_tl, hδ]
      exact div_nonneg hr_pos'.le htl_pos.le
    have h_rpow : (r / thetaLocal) ^ eta ≤ (hairbrushRobustQ δ aCore eta / 2) ^ eta := by
      gcongr
    have h9 : (near_F.card : ℝ) ≤ (hairbrushRobustQ δ aCore eta / 2) ^ eta * (through_F.card : ℝ) := by
      calc (near_F.card : ℝ)
        ≤ (r / thetaLocal) ^ eta * (through_F.card : ℝ) := h4'
      _ ≤ (hairbrushRobustQ δ aCore eta / 2) ^ eta * (through_F.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right h_rpow (by positivity)
    have h10 : (hairbrushRobustQ δ aCore eta / 2) ^ eta =
        (hairbrushRobustQ δ aCore eta) ^ eta / (2 : ℝ) ^ eta := by
      rw [div_rpow (by linarith) (by norm_num)]
    rw [h10] at h9
    have h11 : (hairbrushRobustQ δ aCore eta) ^ eta = δ ^ aCore / 8 :=
      hairbrushRobustQ_pow_eta hδ haCore heta
    rw [h11] at h9
    let near_Z := through_Z.filter (fun U => hairbrushAcuteAngle T U < r)
    have h_near_Z_sub_near_F : near_Z ⊆ near_F := by
      intro U hU
      have hU_in_throughZ : U ∈ through_Z := (Finset.mem_filter.mp hU).1
      have hU_in_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU_in_throughZ).1
      have hxU : x ∈ core.Z.carrier U := (Finset.mem_filter.mp hU_in_throughZ).2
      have hU_in_F : U ∈ F := core.F3_subset hU_in_F3
      have hxUY : x ∈ Y.carrier U := core.Z_subset_Y U hU_in_F3 hxU
      have h_angle_lt : hairbrushAcuteAngle T U < r := (Finset.mem_filter.mp hU).2
      have h_angle_le : hairbrushAcuteDirectionAngle U.direction T.direction ≤ r := by
        have h10 : hairbrushAcuteAngle U T = hairbrushAcuteDirectionAngle U.direction T.direction := by rfl
        have h_symm : hairbrushAcuteAngle T U = hairbrushAcuteAngle U T := hairbrushAcuteAngle_symm' T U
        rw [←h10, ←h_symm] <;> exact h_angle_lt.le
      simp only [near_F, through_F, Finset.mem_filter] <;> exact ⟨⟨hU_in_F, hxUY⟩, h_angle_le⟩
    have h12 : (near_Z.card : ℝ) ≤ (near_F.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_near_Z_sub_near_F
    have hT_in_throughF : T ∈ through_F := by
      simp only [through_F, Finset.mem_filter]
      exact ⟨core.F3_subset hT, core.Z_subset_Y T hT hxT⟩
    have h13 : 0 < through_F.card := Finset.card_pos.mpr ⟨T, hT_in_throughF⟩
    have h_alphaOld_ne_top : core.alphaOld ≠ ⊤ := by
      by_contra h_top
      have h14 : core.alphaOld * (through_F.card : ENNReal) ≤ (through_Z.card : ENNReal) :=
        core.multiplicity_retention x hx
      rw [h_top] at h14
      have h15 : (⊤ : ENNReal) * (through_F.card : ENNReal) = ⊤ := by
        rw [ENNReal.top_mul] <;> simp [h13.ne']
      rw [h15] at h14
      have h16 : (through_Z.card : ENNReal) ≠ ⊤ := by simp
      have h_eq_top : (through_Z.card : ENNReal) = ⊤ := top_unique h14
      exact h16 h_eq_top
    have h_alphaOld_pos : 0 < core.alphaOld := by
      have h15 : Kakeya.realRpowENN δ aCore ≤ core.alphaOld := core.alphaOld_lower
      have h16 : 0 < Kakeya.realRpowENN δ aCore := by
        dsimp only [Kakeya.realRpowENN]
        have h17 : 0 < δ ^ aCore := by positivity
        positivity
      exact lt_of_lt_of_le h16 h15
    set aOld : ℝ := core.alphaOld.toReal with haOld_def
    have haOld_pos : 0 < aOld := by
      rw [haOld_def]
      have h_ne_zero : core.alphaOld ≠ 0 := h_alphaOld_pos.ne'
      have h_ne_top : core.alphaOld ≠ ⊤ := h_alphaOld_ne_top
      exact ENNReal.toReal_pos h_ne_zero h_ne_top
    have h17_enn : core.alphaOld * (through_F.card : ENNReal) ≤ (through_Z.card : ENNReal) :=
      core.multiplicity_retention x hx
    have h17_mul_ne_top : (core.alphaOld * (through_F.card : ENNReal)) ≠ ⊤ :=
      ENNReal.mul_ne_top h_alphaOld_ne_top (by simp)
    have h17 : aOld * (through_F.card : ℝ) ≤ (through_Z.card : ℝ) := by
      have h_conv : (core.alphaOld * (through_F.card : ENNReal)).toReal ≤ ((through_Z.card : ENNReal)).toReal :=
        (ENNReal.toReal_le_toReal h17_mul_ne_top (by simp)).mpr h17_enn
      have h_left : (core.alphaOld * (through_F.card : ENNReal)).toReal = aOld * (through_F.card : ℝ) := by
        rw [ENNReal.toReal_mul, haOld_def] <;> rfl
      rw [h_left] at h_conv
      simpa using h_conv
    have h18 : (through_F.card : ℝ) ≤ (through_Z.card : ℝ) / aOld := by
      have h_eq : aOld * (through_F.card : ℝ) / aOld = (through_F.card : ℝ) := by
        field_simp [haOld_pos.ne'] <;> ring
      have h : aOld * (through_F.card : ℝ) ≤ (through_Z.card : ℝ) := h17
      have h' : aOld * (through_F.card : ℝ) / aOld ≤ (through_Z.card : ℝ) / aOld := by gcongr
      rw [h_eq] at h'
      exact h'
    have h21 : δ ^ aCore ≤ aOld := by
      have h22 : Kakeya.realRpowENN δ aCore ≤ core.alphaOld := core.alphaOld_lower
      have h23 : Kakeya.realRpowENN δ aCore = ENNReal.ofReal (δ ^ aCore) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h23] at h22
      have h24 : (ENNReal.ofReal (δ ^ aCore)).toReal ≤ core.alphaOld.toReal :=
        (ENNReal.toReal_le_toReal (by simp) h_alphaOld_ne_top).mpr h22
      have h25 : (ENNReal.ofReal (δ ^ aCore)).toReal = δ ^ aCore := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      rw [h25] at h24
      exact h24
    have h28 : 0 < δ ^ aCore := by positivity
    have h24 : (near_Z.card : ℝ) ≤ (through_Z.card : ℝ) / (8 * (2 : ℝ) ^ eta) := by
      calc (near_Z.card : ℝ)
        ≤ (near_F.card : ℝ) := h12
      _ ≤ ((δ ^ aCore / 8) / (2 : ℝ) ^ eta) * (through_F.card : ℝ) := h9
      _ ≤ ((δ ^ aCore / 8) / (2 : ℝ) ^ eta) * ((through_Z.card : ℝ) / aOld) := by gcongr
      _ = (through_Z.card : ℝ) * ((δ ^ aCore / 8) / ((2 : ℝ) ^ eta * aOld)) := by ring
      _ ≤ (through_Z.card : ℝ) * ((δ ^ aCore / 8) / ((2 : ℝ) ^ eta * δ ^ aCore)) := by gcongr
      _ = (through_Z.card : ℝ) / (8 * (2 : ℝ) ^ eta) := by
        field_simp [h28.ne'] <;> ring
    have h30 : 0 < (through_Z.card : ℝ) := by exact_mod_cast (show 0 < through_Z.card from by omega)
    have h31 : (1 : ℝ) < (2 : ℝ) ^ eta := by
      exact one_lt_rpow (by norm_num) (by linarith)
    have h32 : (through_Z.card : ℝ) / (8 * (2 : ℝ) ^ eta) < (through_Z.card : ℝ) / 2 := by
      have h33 : 8 * (2 : ℝ) ^ eta > 2 := by nlinarith
      gcongr
    exact h24.trans_lt h32 |>.le

lemma acute_angle_band_cover (r : ℝ) (hr_pos : 0 < r) (hr_one : r ≤ 1)
    (K : ℕ) (hK : K = Nat.ceil (Real.log (1 / r) / Real.log 2))
    {α : ℝ} (hα1 : r ≤ α) (hα2 : α ≤ Real.pi / 2) :
    ∃ k : ℕ, k ≤ K ∧
      (let σ : ℕ → ℝ := fun j => if j < K then (2 : ℝ)^j * r else 1
       σ k ≤ α ∧ α ≤ 2 * σ k) := by
  let σ : ℕ → ℝ := fun j => if j < K then (2 : ℝ)^j * r else 1
  by_cases hα_ge_one : 1 ≤ α
  · refine ⟨K, le_refl K, ?_⟩
    dsimp only [σ]
    simpa [if_neg (show ¬K < K from by omega)] using
      ⟨hα_ge_one, by linarith [Real.pi_lt_four]⟩
  · have hα_lt_one : α < 1 := by linarith
    have hK_pow : (1 : ℝ) / r ≤ (2 : ℝ)^K := by
      set x : ℝ := Real.log (1 / r) / Real.log 2 with hx
      have h1 : x ≤ (K : ℝ) := by
        rw [hK] <;> exact Nat.le_ceil x
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h3 : Real.log (1 / r) ≤ (K : ℝ) * Real.log 2 := by
        have h4 : Real.log (1 / r) = x * Real.log 2 := by
          dsimp only [x]; field_simp [hlog2_pos.ne'] <;> ring
        rw [h4]; gcongr
      have h5 : 0 < 1 / r := by positivity
      have h6 : Real.log (1 / r) ≤ Real.log ((2 : ℝ)^K) := by
        have h7 : Real.log ((2 : ℝ)^K) = (K : ℝ) * Real.log 2 := by
          simp [Real.log_pow] <;> ring
        rw [h7]; exact h3
      exact (Real.log_le_log_iff h5 (by positivity)).mp h6
    have h_pow1 : (2 : ℝ)^K * r ≥ 1 := by
      have h : (1 : ℝ) / r ≤ (2 : ℝ)^K := hK_pow
      have h' : ((1 : ℝ) / r) * r ≤ (2 : ℝ)^K * r :=
        mul_le_mul_of_nonneg_right h (by linarith)
      have h'' : ((1 : ℝ) / r) * r = 1 := by
        field_simp [hr_pos.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have hK_pos : 0 < K := by
      have hpos : 0 < r := hr_pos
      have hr_lt_one : r < 1 := by linarith [hα1]
      have h1r_gt_one : 1 / r > 1 := one_lt_one_div hr_pos hr_lt_one
      have hlog_pos : 0 < Real.log (1 / r) := Real.log_pos h1r_gt_one
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hx_pos : 0 < Real.log (1 / r) / Real.log 2 := by positivity
      have h : (K : ℝ) > 0 := by
        rw [hK]
        have h2 : 0 < Nat.ceil (Real.log (1 / r) / Real.log 2) := Nat.ceil_pos.mpr hx_pos
        exact_mod_cast h2
      exact_mod_cast h
    let S : Finset ℕ := Finset.filter (fun k : ℕ => (2 : ℝ)^k * r ≤ α) (Finset.range K)
    have h0_in_S : 0 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hK_pos, by simpa using hα1⟩
    have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
    let k := S.max' hS_nonempty
    have hk_in_S : k ∈ S := Finset.max'_mem S hS_nonempty
    have hk_lt : k < K := Finset.mem_range.mp (Finset.mem_filter.mp hk_in_S).1
    have h_pow_k : (2 : ℝ)^k * r ≤ α := (Finset.mem_filter.mp hk_in_S).2
    have h_pow_k1 : α < (2 : ℝ)^(k + 1) * r := by
      by_cases h_kK : k + 1 = K
      · rw [h_kK]
        have h2 : (1 : ℝ) ≤ (2 : ℝ)^K * r := h_pow1
        have h3 : α < 1 := hα_lt_one
        linarith
      · have h_k1_lt_K : k + 1 < K := by omega
        by_contra h
        have h' : (2 : ℝ)^(k + 1) * r ≤ α := by linarith
        have h_range : k + 1 ∈ Finset.range K := by
          simpa [Finset.mem_range] using h_k1_lt_K
        have h_k1_in_S : k + 1 ∈ S := by
          simp only [S, Finset.mem_filter] <;> exact ⟨h_range, h'⟩
        have h_le : k + 1 ≤ k := Finset.le_max' S (k + 1) h_k1_in_S
        exact False.elim (Nat.not_succ_le_self k h_le)
    refine ⟨k, le_of_lt hk_lt, ?_⟩
    have hσk : σ k = (2 : ℝ)^k * r := by
      simp [σ, if_pos hk_lt]
    have h_goal : σ k ≤ α ∧ α ≤ 2 * σ k := by
      rw [hσk]
      constructor
      · exact h_pow_k
      · have h_eq : (2 : ℝ)^(k + 1) * r = 2 * ((2 : ℝ)^k * r) := by ring
        have h : α < 2 * ((2 : ℝ)^k * r) := by rw [←h_eq]; exact h_pow_k1
        exact le_of_lt h
    dsimp only
    exact h_goal

lemma measurable_bandCount {δ : ℝ} {F3 : Kakeya.TubeFamily δ}
    (T : Kakeya.DeltaTube δ) (sigma : ℝ) :
    Measurable fun x : Point3 =>
      (F3.filter fun U =>
        U ≠ T ∧ x ∈ U.carrier ∧
        sigma ≤ hairbrushAcuteAngle T U ∧
        hairbrushAcuteAngle T U ≤ 2 * sigma).card := by
  let P : Kakeya.DeltaTube δ → Prop := fun U =>
    U ≠ T ∧ sigma ≤ hairbrushAcuteAngle T U ∧ hairbrushAcuteAngle T U ≤ 2 * sigma
  have h_eq : (fun x : Point3 =>
      (F3.filter (fun U => P U ∧ x ∈ U.carrier)).card) =
      fun x : Point3 => ∑ U ∈ F3,
        if P U ∧ x ∈ U.carrier then (1 : ℕ) else 0 := by
    funext x
    have h_filter : (F3.filter (fun U => P U ∧ x ∈ U.carrier)).card =
        ∑ U ∈ F3, if P U ∧ x ∈ U.carrier then (1 : ℕ) else 0 := by
      rw [Finset.sum_ite] <;> simp
    exact h_filter
  have h_main : Measurable (fun x : Point3 =>
      (F3.filter (fun U => P U ∧ x ∈ U.carrier)).card) := by
    rw [h_eq]
    apply Finset.measurable_sum
    intro U hU
    have hms : MeasurableSet (U.carrier) := by
      unfold Kakeya.DeltaTube.carrier
      exact Metric.isClosed_cthickening.measurableSet
    by_cases hP : P U
    · have h_fun : (fun x : Point3 => if P U ∧ x ∈ U.carrier then (1 : ℕ) else 0) =
          (fun x : Point3 => if x ∈ U.carrier then (1 : ℕ) else 0) := by
        funext x; simp [hP]
      rw [h_fun]
      exact Measurable.ite hms measurable_const measurable_const
    · have h_fun : (fun x : Point3 => if P U ∧ x ∈ U.carrier then (1 : ℕ) else 0) =
          (fun _ : Point3 => (0 : ℕ)) := by
        funext x; simp [hP]
      rw [h_fun]; exact measurable_const
  have h_final : (fun x : Point3 =>
      (F3.filter (fun U =>
        U ≠ T ∧ x ∈ U.carrier ∧
          sigma ≤ hairbrushAcuteAngle T U ∧
          hairbrushAcuteAngle T U ≤ 2 * sigma)).card) =
      (fun x : Point3 => (F3.filter (fun U => P U ∧ x ∈ U.carrier)).card) := by
    funext x
    congr
    funext U
    simp [P] <;> tauto
  rw [h_final]
  exact h_main

lemma log_bound_key (δ r : ℝ) (hδ_pos : 0 < δ) (hδ : δ ≤ 1 / 1000)
    (hr : δ ≤ r) :
    2 * ((Nat.ceil (Real.log (1 / r) / Real.log 2)) + 1) ≤ (Real.log (1 / δ)) ^ 2 := by
  have h1 : 0 < r := by linarith
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log1δ_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    have h : 1 / δ > 1 := by apply one_lt_one_div <;> linarith
    exact h
  set x : ℝ := Real.log (1 / δ) with hx_def
  have h_1δ_ge1000 : 1 / δ ≥ 1000 := by
    calc 1 / δ ≥ 1 / (1 / 1000) := by gcongr
    _ = 1000 := by norm_num
  have hx_ge_log1000 : x ≥ Real.log 1000 := by
    rw [hx_def]
    exact Real.log_le_log (by positivity) h_1δ_ge1000
  have h_log2_ge_half : Real.log 2 ≥ 1 / 2 := by
    have h15 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have h_inv_log2_le2 : 1 / Real.log 2 ≤ 2 := by
    have h4 : 1 / Real.log 2 ≤ 1 / (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) h_log2_ge_half
    have h5 : 1 / (1 / 2 : ℝ) = 2 := by norm_num
    rw [h5] at h4; exact h4
  have hx_gt6 : x > 6 := by
    have h_log2_gt23 : Real.log 2 > (2 / 3 : ℝ) := by
      have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have h_log8_gt2 : Real.log 8 > 2 := by
      have h_eq : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] <;> ring
      rw [h_eq]; linarith
    have h_log10_gt2 : Real.log 10 > 2 := by
      have h : Real.log 10 > Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
      linarith [h_log8_gt2]
    have h_log1000_gt6 : Real.log 1000 > 6 := by
      have h9 : Real.log 1000 = 3 * Real.log 10 := by
        rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow] <;> ring
      rw [h9]
      linarith [h_log10_gt2]
    linarith [hx_ge_log1000, h_log1000_gt6]
  have h_main_ineq : 2 * (x / Real.log 2 + 2) ≤ x ^ 2 := by
    have h2 : x / Real.log 2 ≤ 2 * x := by
      have h6 : x / Real.log 2 = x * (1 / Real.log 2) := by ring
      rw [h6]
      have hx_nonneg : 0 ≤ x := by linarith [hx_gt6]
      have h7 : x * (1 / Real.log 2) ≤ x * 2 :=
        mul_le_mul_of_nonneg_left h_inv_log2_le2 hx_nonneg
      linarith
    have h1 : 2 * (x / Real.log 2 + 2) ≤ 4 * x + 4 := by linarith
    have h3 : 4 * x + 4 ≤ x ^ 2 := by nlinarith
    linarith
  by_cases h_case : r ≤ 1
  · have h_1r_ge1 : 1 / r ≥ 1 := by apply one_le_one_div <;> linarith
    have h_log1r_nonneg : 0 ≤ Real.log (1 / r) := Real.log_nonneg h_1r_ge1
    have h21 : 1 / r ≤ 1 / δ := by apply one_div_le_one_div_of_le <;> linarith
    have h2 : Real.log (1 / r) ≤ Real.log (1 / δ) := by
      apply Real.log_le_log
      · positivity
      · exact h21
    set y : ℝ := Real.log (1 / r) / Real.log 2 with hy_def
    have hy_nonneg : 0 ≤ y := by apply div_nonneg <;> linarith
    have h3 : (Nat.ceil y : ℝ) < y + 1 := Nat.ceil_lt_add_one hy_nonneg
    have h4 : y ≤ x / Real.log 2 := by
      rw [hy_def, hx_def] <;> gcongr
    have h5 : (Nat.ceil y : ℝ) + 1 ≤ x / Real.log 2 + 2 := by linarith
    have h6 : (2 : ℝ) * ((Nat.ceil y : ℝ) + 1) ≤ 2 * (x / Real.log 2 + 2) := by gcongr
    have h7 : (2 : ℝ) * ((Nat.ceil y : ℝ) + 1) ≤ x ^ 2 := by linarith [h_main_ineq, h6]
    exact_mod_cast h7
  · have hr_gt1 : r > 1 := by linarith
    have h_1r_lt1 : 1 / r < 1 := by
      have h_pos : 0 < r := by linarith
      exact (div_lt_one h_pos).mpr (by linarith)
    have h_log1r_neg : Real.log (1 / r) < 0 := Real.log_neg (by positivity) h_1r_lt1
    have h_y_neg : Real.log (1 / r) / Real.log 2 < 0 := by
      apply div_neg_of_neg_of_pos h_log1r_neg h_log2_pos
    have h_ceil_zero : Nat.ceil (Real.log (1 / r) / Real.log 2) = 0 := by
      apply Nat.ceil_eq_zero.mpr
      linarith
    rw [h_ceil_zero]
    have h9 : (2 : ℝ) ≤ x ^ 2 := by nlinarith
    exact_mod_cast h9

lemma acute_lossFactor_bound (δ r : ℝ)
    (hδ : 0 < δ) (hδ1000 : δ ≤ 1 / 1000)
    (hr_ge_delta : δ ≤ r) :
    let K := Nat.ceil (Real.log (1 / r) / Real.log 2)
    (K : ℝ) + 1 ≤ 1000 * Real.log (1 / δ) ^ 2 := by
  let K := Nat.ceil (Real.log (1 / r) / Real.log 2)
  have h1 : 2 * ((K : ℝ) + 1) ≤ Real.log (1 / δ) ^ 2 :=
    log_bound_key δ r hδ hδ1000 hr_ge_delta
  have h2 : (K : ℝ) + 1 ≤ Real.log (1 / δ) ^ 2 := by linarith
  have h3 : Real.log (1 / δ) ^ 2 ≤ 1000 * Real.log (1 / δ) ^ 2 := by
    have h4 : 0 ≤ Real.log (1 / δ) ^ 2 := by positivity
    nlinarith
  linarith

lemma acute_mass_pigeonhole {B : ℕ} (hB_pos : 0 < B)
    {S : Set Point3} (hS_meas : MeasurableSet S) (hS_top : volume S ≠ ⊤)
    (A : ℕ → Set Point3) (hA_meas : ∀ k ∈ Finset.range B, MeasurableSet (A k))
    (hA_sub : ∀ k ∈ Finset.range B, A k ⊆ S)
    (hcover : S ⊆ ⋃ k ∈ Finset.range B, A k) :
    ∃ k ∈ Finset.range B, volume S / (B : ENNReal) ≤ volume (A k) := by
  have h_sum : volume S ≤ ∑ k ∈ Finset.range B, volume (A k) := by
    calc volume S
      ≤ volume (⋃ k ∈ Finset.range B, A k) := measure_mono hcover
    _ ≤ ∑ k ∈ Finset.range B, volume (A k) := measure_biUnion_finset_le (Finset.range B) A
  rcases Kakeya.Hairbrush.ennreal_sum_pigeonhole hS_top h_sum (Finset.nonempty_range_iff.mpr hB_pos.ne') with ⟨k, hk_in, hk_ge⟩
  refine ⟨k, hk_in, ?_⟩
  have h_card : (Finset.range B).card = B := by simp
  rw [h_card] at hk_ge
  exact hk_ge

end Kakeya.Assouad
