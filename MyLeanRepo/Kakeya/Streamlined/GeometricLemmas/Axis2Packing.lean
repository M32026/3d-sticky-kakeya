import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PhaseSpaceGridIntercept
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlaneIntercept
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlankDirectionBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.InterceptBounds
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.Axis2Data
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CloseAxialTubes

/-!
# Axis-2 positive packing bound

For tubes with `u_2 ≥ 1/2` in frame coordinates, apply the intercept-based
phase-space grid packing theorem with bacon's closeness lemma.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

open Classical Kakeya.Streamlined

/-- In positive-axis case, normalized data equals original data. -/
lemma tubePlaneData_pos_case {p u : Point3} (data : TubePlaneData p u)
    (hpos : 0 < u 2) (hu : ‖u‖ = 1) : data.p' = p ∧ data.u' = u := by
  have h_u_ne_zero : u ≠ 0 := by
    intro h
    have h9 : ‖u‖ = 0 := by rw [h] <;> simp
    rw [h9] at hu <;> norm_num at hu
  have h_u' : data.u' = u := by
    rcases data.h_u'_eq with (h | h)
    · exact h
    · have h1 : data.u' 2 = -(u 2) := by rw [h] <;> simp
      have h2 : data.u' 2 < 0 := by rw [h1] <;> linarith
      linarith [data.hu'2_pos]
  have h_p' : data.p' = p := by
    rcases data.h_p'_eq with (h | h)
    · exact h
    · have h_q_in : data.q ∈ Set.image (fun t : ℝ => p + t • u) (Set.Icc (0 : ℝ) 1) := by
        have h1 : data.q ∈ Set.image (fun t : ℝ => data.p' + t • data.u') (Set.Icc (0 : ℝ) 1) := by
          refine ⟨data.t0, ⟨data.h_t0_pos.le, data.h_t0_le_one⟩, ?_⟩
          rw [data.h_q_def]
        rw [data.h_segment] at h1
        exact h1
      rcases h_q_in with ⟨s, hs, h_eq⟩
      have h_q_eq : data.q = p + s • u := h_eq.symm
      have h_q_def2 : data.q = (p + u) + data.t0 • u := by
        rw [data.h_q_def, h, h_u'] <;> ring
      have h_eq2 : (p + u) + data.t0 • u = p + s • u := by
        calc (p + u) + data.t0 • u = data.q := h_q_def2.symm
          _ = p + s • u := h_q_eq
      have h_eq3 : (1 + data.t0) • u = s • u := by
        have h' : (p + u + data.t0 • u) - p = (p + s • u) - p := by rw [h_eq2]
        have h_simp : (p + u + data.t0 • u) - p = u + data.t0 • u := by
          simp [add_assoc] <;> abel
        have h_simp2 : (p + s • u) - p = s • u := by simp
        rw [h_simp, h_simp2] at h'
        have h_final : u + data.t0 • u = (1 + data.t0) • u := by
          rw [add_smul] <;> simp
        exact h_final.symm.trans h'
      have h_inj : Function.Injective (fun c : ℝ => c • u) := by
        intro c d hcd
        have h6 : (c - d) • u = 0 := by
          have h7 : c • u = d • u := hcd
          have h8 : c • u - d • u = 0 := by rw [h7] <;> simp
          simpa [sub_smul] using h8
        have h9 : ‖(c - d) • u‖ = 0 := by rw [h6] <;> simp
        have h10 : |c - d| * ‖u‖ = 0 := by simpa [norm_smul] using h9
        have h11 : ‖u‖ = 1 := hu
        rw [h11] at h10
        have h12 : |c - d| = 0 := by linarith
        have h13 : c - d = 0 := by simpa [abs_eq_zero] using h12
        linarith
      have h_eq5 : 1 + data.t0 = s := h_inj h_eq3
      linarith [data.h_t0_pos, hs.2]
  exact ⟨h_p', h_u'⟩

/-- Packing bound for tubes with positive axis-2 dominance. -/
lemma axis2_positive_packing_bound
    {δ a b A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    {plank : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    (hdim : plank.HasDimensionsInFrame frame a b 1 A)
    {F : Kakeya.TubeFamily δ}
    (hdistinct : F.IsEssentiallyDistinct)
    (hcontain : ∀ T ∈ F, T.carrier ⊆ plank.carrier)
    (h_axis2_pos : ∀ T ∈ F, (frame.symm.linearIsometryEquiv T.direction) 2 ≥ 1 / 2)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    F.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (2 * A * a) / δ + 2) * (200 * (2 * A * b) / δ + 2) * 8 *
      (200 * (A * a) / δ + 2) * (200 * (A * b) / δ + 2)) := by
  let pF (T : DeltaTube δ) : Point3 := frame.symm T.base
  let uF (T : DeltaTube δ) : Point3 := frame.symm.linearIsometryEquiv T.direction
  let hasAxis2 (T : DeltaTube δ) : Prop := |uF T 2| ≥ 1 / 2

  have h_axis2 : ∀ T ∈ F, hasAxis2 T := by
    intro T hT
    dsimp only [hasAxis2]
    have h : uF T 2 ≥ 1 / 2 := h_axis2_pos T hT
    have h' : |uF T 2| ≥ 1 / 2 := by
      rw [abs_of_nonneg (by linarith)]
      exact h
    exact h'

  have hA_nonneg : 0 ≤ A := by linarith
  have ha_nonneg : 0 ≤ a := by linarith [hdim.1]
  have hb_nonneg : 0 ≤ b := by linarith [hdim.1, hdim.2.1]

  have h_norm_unit (T : DeltaTube δ) : ‖uF T‖ = 1 := by
    have h1 : ‖uF T‖ = ‖T.direction‖ := frame.symm.linearIsometryEquiv.norm_map T.direction
    rw [h1, T.direction_unit]

  let getData (T : DeltaTube δ) (h : hasAxis2 T) : TubePlaneData (pF T) (uF T) :=
    computeTubePlaneData (pF T) (uF T) h (h_norm_unit T)

  let plane_idx (T : DeltaTube δ) : ℕ :=
    if h : hasAxis2 T then ((getData T h).k + (Nat.ceil A : ℤ)).toNat else 0
  let q1 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).q 0 else 0
  let q2 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).q 1 else 0
  let t0 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).t0 else 0
  let du1 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).u' 0 else 0
  let du2 (T : DeltaTube δ) : ℝ :=
    if h : hasAxis2 T then (getData T h).u' 1 else 0

  have h_plane : ∀ T ∈ F, plane_idx T < 2 * Nat.ceil A + 2 := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : plane_idx T = ((data.k + (Nat.ceil A : ℤ)).toNat) := by
      dsimp only [plane_idx]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p'2 : |data.p' 2| ≤ A / 2 := h_endpoints.1.2.2
    have hlo : -A / 2 ≤ data.p' 2 := by linarith [abs_le.mp h_p'2]
    have hhi : data.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
    have h2 : (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 :=
      planeIndex_nat_lt' (data.p' 2) A hA_nonneg hlo hhi
    have h3 : (data.k + (Nat.ceil A : ℤ)).toNat = (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat := by
      apply congr_arg (fun x : ℤ => (x + (Nat.ceil A : ℤ)).toNat)
      exact_mod_cast data.h_k_def
    rw [h3]; exact h2

  have h_q1_bound : ∀ T ∈ F, |q1 T| ≤ 2 * A * a := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : q1 T = data.q 0 := by dsimp only [q1]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p0 : |data.p' 0| ≤ A * a / 2 := h_endpoints.1.1
    have h_p1 : |data.p' 1| ≤ A * b / 2 := h_endpoints.1.2.1
    have h_u0 : |data.u' 0| ≤ A * a := by
      have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 0 - data.p' 0|
        ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
      _ ≤ A * a / 2 + A * a / 2 := add_le_add h_endpoints.2.1 h_endpoints.1.1
      _ = A * a := by ring
    have h_u1 : |data.u' 1| ≤ A * b := by
      have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 1 - data.p' 1|
        ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
      _ ≤ A * b / 2 + A * b / 2 := add_le_add h_endpoints.2.2.1 h_endpoints.1.2.1
      _ = A * b := by ring
    have h_t0_pos : 0 ≤ data.t0 := data.h_t0_pos.le
    have h_t0_le_one : data.t0 ≤ 1 := data.h_t0_le_one
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def]
    have h_bound := plank_intercept_bounds data.p' data.u' data.t0 A a b hA_nonneg
      ha_nonneg hb_nonneg h_p0 h_p1 h_u0 h_u1 h_t0_pos h_t0_le_one
    have h : |(data.p' + data.t0 • data.u') 0| ≤ 3 * A * a / 2 := h_bound.1
    have h_final : 3 * A * a / 2 ≤ 2 * A * a := by nlinarith
    linarith

  have h_q2_bound : ∀ T ∈ F, |q2 T| ≤ 2 * A * b := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : q2 T = data.q 1 := by dsimp only [q2]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_p0 : |data.p' 0| ≤ A * a / 2 := h_endpoints.1.1
    have h_p1 : |data.p' 1| ≤ A * b / 2 := h_endpoints.1.2.1
    have h_u0 : |data.u' 0| ≤ A * a := by
      have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 0 - data.p' 0|
        ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
      _ ≤ A * a / 2 + A * a / 2 := add_le_add h_endpoints.2.1 h_endpoints.1.1
      _ = A * a := by ring
    have h_u1 : |data.u' 1| ≤ A * b := by
      have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
      rw [h_eq1]
      calc |(data.p' + data.u') 1 - data.p' 1|
        ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
      _ ≤ A * b / 2 + A * b / 2 := add_le_add h_endpoints.2.2.1 h_endpoints.1.2.1
      _ = A * b := by ring
    have h_t0_pos : 0 ≤ data.t0 := data.h_t0_pos.le
    have h_t0_le_one : data.t0 ≤ 1 := data.h_t0_le_one
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def]
    have h_bound := plank_intercept_bounds data.p' data.u' data.t0 A a b hA_nonneg
      ha_nonneg hb_nonneg h_p0 h_p1 h_u0 h_u1 h_t0_pos h_t0_le_one
    have h : |(data.p' + data.t0 • data.u') 1| ≤ 3 * A * b / 2 := h_bound.2
    have h_final : 3 * A * b / 2 ≤ 2 * A * b := by nlinarith
    linarith

  have h_t0_bound : ∀ T ∈ F, t0 T ∈ Set.Icc 0 1 := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : t0 T = data.t0 := by dsimp only [t0]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    exact ⟨data.h_t0_pos.le, data.h_t0_le_one⟩

  have h_du1_bound : ∀ T ∈ F, |du1 T| ≤ A * a := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : du1 T = data.u' 0 := by dsimp only [du1]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_eq1 : data.u' 0 = (data.p' + data.u') 0 - data.p' 0 := by simp
    rw [h_eq1]
    calc |(data.p' + data.u') 0 - data.p' 0|
      ≤ |(data.p' + data.u') 0| + |data.p' 0| := abs_sub _ _
    _ ≤ A * a / 2 + A * a / 2 := add_le_add h_endpoints.2.1 h_endpoints.1.1
    _ = A * a := by ring

  have h_du2_bound : ∀ T ∈ F, |du2 T| ≤ A * b := by
    intro T hT
    have h_dom : hasAxis2 T := h_axis2 T hT
    let data := getData T h_dom
    have h_eq : du2 T = data.u' 1 := by dsimp only [du2]; rw [dif_pos h_dom] <;> rfl
    rw [h_eq]
    have h_endpoints := normalized_endpoints_in_box T plank frame a b A hdim
      (hcontain T hT) (pF T) (uF T) data.p' data.u' rfl rfl data.h_segment data.h_p'_eq
    have h_eq1 : data.u' 1 = (data.p' + data.u') 1 - data.p' 1 := by simp
    rw [h_eq1]
    calc |(data.p' + data.u') 1 - data.p' 1|
      ≤ |(data.p' + data.u') 1| + |data.p' 1| := abs_sub _ _
    _ ≤ A * b / 2 + A * b / 2 := add_le_add h_endpoints.2.2.1 h_endpoints.1.2.1
    _ = A * b := by ring

  have h_close : ∀ (T1 T2 : DeltaTube δ), T1 ∈ F → T2 ∈ F →
      plane_idx T1 = plane_idx T2 →
      |q1 T1 - q1 T2| ≤ δ / 100 →
      |q2 T1 - q2 T2| ≤ δ / 100 →
      |t0 T1 - t0 T2| ≤ 1 / 8 →
      |du1 T1 - du1 T2| ≤ δ / 100 →
      |du2 T1 - du2 T2| ≤ δ / 100 →
      ¬ T1.EssentiallyDistinct T2 := by
    intro T1 T2 hT1 hT2 h_plane_eq h_q1_close h_q2_close h_t0_close h_du1_close h_du2_close
    have h_dom1 : hasAxis2 T1 := h_axis2 T1 hT1
    have h_dom2 : hasAxis2 T2 := h_axis2 T2 hT2
    let data1 := getData T1 h_dom1
    let data2 := getData T2 h_dom2

    have hpos1 : 0 < uF T1 2 := by linarith [h_axis2_pos T1 hT1]
    have hpos2 : 0 < uF T2 2 := by linarith [h_axis2_pos T2 hT2]
    have h_case1 := tubePlaneData_pos_case data1 hpos1 (h_norm_unit T1)
    have h_case2 := tubePlaneData_pos_case data2 hpos2 (h_norm_unit T2)

    have h_k_eq : data1.k = data2.k := by
      have h1 : ((data1.k + (Nat.ceil A : ℤ)).toNat) = ((data2.k + (Nat.ceil A : ℤ)).toNat) := by
        have hpi1 : plane_idx T1 = ((data1.k + (Nat.ceil A : ℤ)).toNat) := by
          dsimp only [plane_idx]; rw [dif_pos h_dom1] <;> rfl
        have hpi2 : plane_idx T2 = ((data2.k + (Nat.ceil A : ℤ)).toNat) := by
          dsimp only [plane_idx]; rw [dif_pos h_dom2] <;> rfl
        rw [hpi1, hpi2] at h_plane_eq
        exact h_plane_eq
      have h_nn1 : 0 ≤ data1.k + (Nat.ceil A : ℤ) := by
        have h_p'2 : |data1.p' 2| ≤ A / 2 := (normalized_endpoints_in_box T1 plank frame a b A hdim
          (hcontain T1 hT1) (pF T1) (uF T1) data1.p' data1.u' rfl rfl data1.h_segment data1.h_p'_eq).1.2.2
        have hlo : -A / 2 ≤ data1.p' 2 := by linarith [abs_le.mp h_p'2]
        have hhi : data1.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
        exact planeIndex_nat_nonneg' (data1.p' 2) A hA_nonneg hlo hhi
      have h_nn2 : 0 ≤ data2.k + (Nat.ceil A : ℤ) := by
        have h_p'2 : |data2.p' 2| ≤ A / 2 := (normalized_endpoints_in_box T2 plank frame a b A hdim
          (hcontain T2 hT2) (pF T2) (uF T2) data2.p' data2.u' rfl rfl data2.h_segment data2.h_p'_eq).1.2.2
        have hlo : -A / 2 ≤ data2.p' 2 := by linarith [abs_le.mp h_p'2]
        have hhi : data2.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
        exact planeIndex_nat_nonneg' (data2.p' 2) A hA_nonneg hlo hhi
      have h_eq_int : data1.k + (Nat.ceil A : ℤ) = data2.k + (Nat.ceil A : ℤ) := by
        have h_toNat1 : ((data1.k + (Nat.ceil A : ℤ)).toNat : ℤ) = data1.k + (Nat.ceil A : ℤ) :=
          Int.toNat_of_nonneg h_nn1
        have h_toNat2 : ((data2.k + (Nat.ceil A : ℤ)).toNat : ℤ) = data2.k + (Nat.ceil A : ℤ) :=
          Int.toNat_of_nonneg h_nn2
        have h_eq_nat : (data1.k + (Nat.ceil A : ℤ)).toNat = (data2.k + (Nat.ceil A : ℤ)).toNat := h1
        have h : ((data1.k + (Nat.ceil A : ℤ)).toNat : ℤ) = ((data2.k + (Nat.ceil A : ℤ)).toNat : ℤ) := by
          exact_mod_cast h_eq_nat
        rw [h_toNat1, h_toNat2] at h
        exact h
      linarith

    have hplane : data1.q 2 = data2.q 2 := by
      have h1 : data1.q 2 = (data1.k : ℝ) / 2 := data1.h_q2
      have h2 : data2.q 2 = (data2.k : ℝ) / 2 := data2.h_q2
      rw [h1, h2, h_k_eq]

    have h_hq0 : |(data1.q - data2.q) 0| ≤ δ / 100 := by
      have h_eq1 : q1 T1 = data1.q 0 := by dsimp only [q1]; rw [dif_pos h_dom1] <;> rfl
      have h_eq2 : q1 T2 = data2.q 0 := by dsimp only [q1]; rw [dif_pos h_dom2] <;> rfl
      rw [h_eq1, h_eq2] at h_q1_close
      simpa using h_q1_close
    have h_hq1 : |(data1.q - data2.q) 1| ≤ δ / 100 := by
      have h_eq1 : q2 T1 = data1.q 1 := by dsimp only [q2]; rw [dif_pos h_dom1] <;> rfl
      have h_eq2 : q2 T2 = data2.q 1 := by dsimp only [q2]; rw [dif_pos h_dom2] <;> rfl
      rw [h_eq1, h_eq2] at h_q2_close
      simpa using h_q2_close
    have h_htdiff : |data1.t0 - data2.t0| ≤ 1 / 8 := by
      have h_eq1 : t0 T1 = data1.t0 := by dsimp only [t0]; rw [dif_pos h_dom1] <;> rfl
      have h_eq2 : t0 T2 = data2.t0 := by dsimp only [t0]; rw [dif_pos h_dom2] <;> rfl
      rw [h_eq1, h_eq2] at h_t0_close
      exact h_t0_close
    have h_hdir0 : |(data1.u' - data2.u') 0| ≤ δ / 100 := by
      have h_eq1 : du1 T1 = data1.u' 0 := by dsimp only [du1]; rw [dif_pos h_dom1] <;> rfl
      have h_eq2 : du1 T2 = data2.u' 0 := by dsimp only [du1]; rw [dif_pos h_dom2] <;> rfl
      rw [h_eq1, h_eq2] at h_du1_close
      simpa using h_du1_close
    have h_hdir1 : |(data1.u' - data2.u') 1| ≤ δ / 100 := by
      have h_eq1 : du2 T1 = data1.u' 1 := by dsimp only [du2]; rw [dif_pos h_dom1] <;> rfl
      have h_eq2 : du2 T2 = data2.u' 1 := by dsimp only [du2]; rw [dif_pos h_dom2] <;> rfl
      rw [h_eq1, h_eq2] at h_du2_close
      simpa using h_du2_close

    have h_hu2_1 : data1.u' 2 ≥ 1 / 2 := by
      have h : |data1.u' 2| ≥ 1 / 2 := data1.hu'2_dom
      have hpos : 0 < data1.u' 2 := data1.hu'2_pos
      rw [abs_of_pos hpos] at h
      exact h
    have h_hu2_2 : data2.u' 2 ≥ 1 / 2 := by
      have h : |data2.u' 2| ≥ 1 / 2 := data2.hu'2_dom
      have hpos : 0 < data2.u' 2 := data2.hu'2_pos
      rw [abs_of_pos hpos] at h
      exact h

    have h_hu2_1' : (uF T1) 2 ≥ 1 / 2 := by
      rw [←h_case1.2]
      exact h_hu2_1
    have h_hu2_2' : (uF T2) 2 ≥ 1 / 2 := by
      rw [←h_case2.2]
      exact h_hu2_2

    exact close_axial_tubes_not_distinct hδ hδ1
      frame (pF T1) (uF T1) (pF T2) (uF T2) data1.q data2.q data1.t0 data2.t0
      rfl rfl rfl rfl
      ⟨data1.h_t0_pos.le, data1.h_t0_le_one⟩
      ⟨data2.h_t0_pos.le, data2.h_t0_le_one⟩
      (by rw [data1.h_q_def, h_case1.1, h_case1.2] <;> ring)
      (by rw [data2.h_q_def, h_case2.1, h_case2.2] <;> ring)
      hplane h_hq0 h_hq1 h_htdiff
      (by rw [←h_case1.2, ←h_case2.2] <;> exact h_hdir0)
      (by rw [←h_case1.2, ←h_case2.2] <;> exact h_hdir1)
      h_hu2_1' h_hu2_2' h_capsule_lower h_capsule_upper

  have hR1 : 0 < 2 * A * a := by
    have h1 : 0 < a := hdim.1
    nlinarith
  have hR2 : 0 < 2 * A * b := by
    have h1 : 0 < a := hdim.1
    have h2 : a ≤ b := hdim.2.1
    nlinarith
  have hD1 : 0 < A * a := by
    have h1 : 0 < a := hdim.1
    nlinarith
  have hD2 : 0 < A * b := by
    have h1 : 0 < a := hdim.1
    have h2 : a ≤ b := hdim.2.1
    nlinarith
  exact phase_space_grid_packing_intercept hδ hδ1 hA hdistinct
    (2 * A * a) (2 * A * b) (A * a) (A * b)
    hR1 hR2 hD1 hD2
    (2 * Nat.ceil A + 2)
    plane_idx q1 q2 t0 du1 du2
    h_plane h_q1_bound h_q2_bound h_t0_bound h_du1_bound h_du2_bound h_close



lemma general_positive_packing_bound
    {δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    {F : Kakeya.TubeFamily δ}
    (hdistinct : F.IsEssentiallyDistinct)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p u : DeltaTube δ → Point3)
    (h_p_eq : ∀ T ∈ F, p T = frame.symm T.base)
    (h_u_eq : ∀ T ∈ F, u T = frame.symm.linearIsometryEquiv T.direction)
    (h_norm : ∀ T ∈ F, ‖u T‖ = 1)
    (h_axis2_pos : ∀ T ∈ F, u T 2 ≥ 1 / 2)
    (P1 P2 D1 D2 : ℝ)
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (h_p2_bound : ∀ T ∈ F, |p T 2| ≤ A / 2)
    (h_p0_bound : ∀ T ∈ F, |p T 0| ≤ P1)
    (h_p1_bound : ∀ T ∈ F, |p T 1| ≤ P2)
    (h_u0_bound : ∀ T ∈ F, |u T 0| ≤ D1)
    (h_u1_bound : ∀ T ∈ F, |u T 1| ≤ D2)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    F.enncard ≤ ENNReal.ofReal ((2 * Nat.ceil A + 2 : ℕ) *
      (200 * (P1 + D1) / δ + 2) * (200 * (P2 + D2) / δ + 2) * 8 *
      (200 * D1 / δ + 2) * (200 * D2 / δ + 2)) := by
  let hasAxis2 (T : DeltaTube δ) : Prop := |u T 2| ≥ 1 / 2
  have h_axis2 : ∀ T ∈ F, hasAxis2 T := by
    intro T hT
    have h : u T 2 ≥ 1 / 2 := h_axis2_pos T hT
    have h' : |u T 2| ≥ 1 / 2 := by
      rw [abs_of_nonneg (by linarith)] <;> exact h
    exact h'
  have hA_nonneg : 0 ≤ A := by linarith
  classical
  let getData (T : DeltaTube δ) (hT : T ∈ F) : TubePlaneData (p T) (u T) :=
    computeTubePlaneData (p T) (u T) (h_axis2 T hT) (h_norm T hT)
  let plane_idx (T : DeltaTube δ) : ℕ :=
    if hT : T ∈ F then ((getData T hT).k + (Nat.ceil A : ℤ)).toNat else 0
  let q1 (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then (getData T hT).q 0 else 0
  let q2 (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then (getData T hT).q 1 else 0
  let t0 (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then (getData T hT).t0 else 0
  let du1 (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then (getData T hT).u' 0 else 0
  let du2 (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then (getData T hT).u' 1 else 0
  have h_pos_case (T : DeltaTube δ) (hT : T ∈ F) :
      (getData T hT).p' = p T ∧ (getData T hT).u' = u T := by
    have hpos : 0 < u T 2 := by linarith [h_axis2_pos T hT]
    exact tubePlaneData_pos_case (getData T hT) hpos (h_norm T hT)
  have h_plane : ∀ T ∈ F, plane_idx T < 2 * Nat.ceil A + 2 := by
    intro T hT
    let data := getData T hT
    have h_eq : plane_idx T = ((data.k + (Nat.ceil A : ℤ)).toNat) := by
      unfold plane_idx
      rw [dif_pos hT] <;> rfl
    rw [h_eq]
    have hpc := h_pos_case T hT
    have h_p'2 : |data.p' 2| ≤ A / 2 := by rw [hpc.1]; exact h_p2_bound T hT
    have hlo : -A / 2 ≤ data.p' 2 := by linarith [abs_le.mp h_p'2]
    have hhi : data.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
    have h2 : (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 :=
      planeIndex_nat_lt' (data.p' 2) A hA_nonneg hlo hhi
    have h3 : (data.k + (Nat.ceil A : ℤ)).toNat = (planeIndex (data.p' 2) + (Nat.ceil A : ℤ)).toNat := by
      apply congr_arg (fun x : ℤ => (x + (Nat.ceil A : ℤ)).toNat)
      exact_mod_cast data.h_k_def
    rw [h3]; exact h2
  have h_q1_bound : ∀ T ∈ F, |q1 T| ≤ P1 + D1 := by
    intro T hT
    let data := getData T hT
    have h_eq : q1 T = data.q 0 := by unfold q1; rw [dif_pos hT] <;> rfl
    rw [h_eq]
    have hpc := h_pos_case T hT
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def, hpc.1, hpc.2]
    have h1 : |(p T + data.t0 • u T) 0| ≤ |p T 0| + |(data.t0 • u T) 0| := by
      simpa [Pi.add_apply, Real.norm_eq_abs] using norm_add_le (p T 0) ((data.t0 • u T) 0)
    have h2 : |(data.t0 • u T) 0| ≤ |u T 0| := by
      have h3 : (data.t0 • u T) 0 = data.t0 * u T 0 := by simp
      rw [h3]
      have h4 : |data.t0| ≤ 1 := by
        rw [abs_of_nonneg data.h_t0_pos.le] <;> exact data.h_t0_le_one
      calc |data.t0 * u T 0| = |data.t0| * |u T 0| := by rw [abs_mul]
        _ ≤ 1 * |u T 0| := by gcongr
        _ = |u T 0| := by ring
    linarith [h_p0_bound T hT, h_u0_bound T hT]
  have h_q2_bound : ∀ T ∈ F, |q2 T| ≤ P2 + D2 := by
    intro T hT
    let data := getData T hT
    have h_eq : q2 T = data.q 1 := by unfold q2; rw [dif_pos hT] <;> rfl
    rw [h_eq]
    have hpc := h_pos_case T hT
    have h_q_def : data.q = data.p' + data.t0 • data.u' := data.h_q_def
    rw [h_q_def, hpc.1, hpc.2]
    have h1 : |(p T + data.t0 • u T) 1| ≤ |p T 1| + |(data.t0 • u T) 1| := by
      simpa [Pi.add_apply, Real.norm_eq_abs] using norm_add_le (p T 1) ((data.t0 • u T) 1)
    have h2 : |(data.t0 • u T) 1| ≤ |u T 1| := by
      have h3 : (data.t0 • u T) 1 = data.t0 * u T 1 := by simp
      rw [h3]
      have h4 : |data.t0| ≤ 1 := by
        rw [abs_of_nonneg data.h_t0_pos.le] <;> exact data.h_t0_le_one
      calc |data.t0 * u T 1| = |data.t0| * |u T 1| := by rw [abs_mul]
        _ ≤ 1 * |u T 1| := by gcongr
        _ = |u T 1| := by ring
    linarith [h_p1_bound T hT, h_u1_bound T hT]
  have h_t0_bound : ∀ T ∈ F, t0 T ∈ Set.Icc 0 1 := by
    intro T hT
    let data := getData T hT
    have h_eq : t0 T = data.t0 := by unfold t0; rw [dif_pos hT] <;> rfl
    rw [h_eq]
    exact ⟨data.h_t0_pos.le, data.h_t0_le_one⟩
  have h_du1_bound : ∀ T ∈ F, |du1 T| ≤ D1 := by
    intro T hT
    let data := getData T hT
    have h_eq : du1 T = data.u' 0 := by unfold du1; rw [dif_pos hT] <;> rfl
    rw [h_eq]
    have hpc := h_pos_case T hT
    rw [hpc.2]
    exact h_u0_bound T hT
  have h_du2_bound : ∀ T ∈ F, |du2 T| ≤ D2 := by
    intro T hT
    let data := getData T hT
    have h_eq : du2 T = data.u' 1 := by unfold du2; rw [dif_pos hT] <;> rfl
    rw [h_eq]
    have hpc := h_pos_case T hT
    rw [hpc.2]
    exact h_u1_bound T hT
  have h_close : ∀ (T1 T2 : DeltaTube δ), T1 ∈ F → T2 ∈ F →
      plane_idx T1 = plane_idx T2 →
      |q1 T1 - q1 T2| ≤ δ / 100 →
      |q2 T1 - q2 T2| ≤ δ / 100 →
      |t0 T1 - t0 T2| ≤ 1 / 8 →
      |du1 T1 - du1 T2| ≤ δ / 100 →
      |du2 T1 - du2 T2| ≤ δ / 100 →
      ¬ T1.EssentiallyDistinct T2 := by
    intro T1 T2 hT1 hT2 h_plane_eq h_q1_close h_q2_close h_t0_close h_du1_close h_du2_close
    let data1 := getData T1 hT1
    let data2 := getData T2 hT2
    have hpos1 : 0 < u T1 2 := by linarith [h_axis2_pos T1 hT1]
    have hpos2 : 0 < u T2 2 := by linarith [h_axis2_pos T2 hT2]
    have h_case1 := tubePlaneData_pos_case data1 hpos1 (h_norm T1 hT1)
    have h_case2 := tubePlaneData_pos_case data2 hpos2 (h_norm T2 hT2)
    have h_k_eq : data1.k = data2.k := by
      have hpi1 : plane_idx T1 = ((data1.k + (Nat.ceil A : ℤ)).toNat) := by
        unfold plane_idx; rw [dif_pos hT1] <;> rfl
      have hpi2 : plane_idx T2 = ((data2.k + (Nat.ceil A : ℤ)).toNat) := by
        unfold plane_idx; rw [dif_pos hT2] <;> rfl
      have h_eq : plane_idx T1 = plane_idx T2 := h_plane_eq
      rw [hpi1, hpi2] at h_eq
      have h_nn1 : 0 ≤ data1.k + (Nat.ceil A : ℤ) := by
        have hpc := h_pos_case T1 hT1
        have h_p'2 : |data1.p' 2| ≤ A / 2 := by rw [hpc.1]; exact h_p2_bound T1 hT1
        have hlo : -A / 2 ≤ data1.p' 2 := by linarith [abs_le.mp h_p'2]
        have hhi : data1.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
        exact planeIndex_nat_nonneg' (data1.p' 2) A hA_nonneg hlo hhi
      have h_nn2 : 0 ≤ data2.k + (Nat.ceil A : ℤ) := by
        have hpc := h_pos_case T2 hT2
        have h_p'2 : |data2.p' 2| ≤ A / 2 := by rw [hpc.1]; exact h_p2_bound T2 hT2
        have hlo : -A / 2 ≤ data2.p' 2 := by linarith [abs_le.mp h_p'2]
        have hhi : data2.p' 2 ≤ A / 2 := by linarith [abs_le.mp h_p'2]
        exact planeIndex_nat_nonneg' (data2.p' 2) A hA_nonneg hlo hhi
      have h_eq_int : data1.k + (Nat.ceil A : ℤ) = data2.k + (Nat.ceil A : ℤ) := by
        have h_toNat1 : ((data1.k + (Nat.ceil A : ℤ)).toNat : ℤ) = data1.k + (Nat.ceil A : ℤ) :=
          Int.toNat_of_nonneg h_nn1
        have h_toNat2 : ((data2.k + (Nat.ceil A : ℤ)).toNat : ℤ) = data2.k + (Nat.ceil A : ℤ) :=
          Int.toNat_of_nonneg h_nn2
        have h_eq_nat : (data1.k + (Nat.ceil A : ℤ)).toNat = (data2.k + (Nat.ceil A : ℤ)).toNat := by
          rw [hpi1, hpi2] at h_plane_eq; exact h_plane_eq
        have h : ((data1.k + (Nat.ceil A : ℤ)).toNat : ℤ) = ((data2.k + (Nat.ceil A : ℤ)).toNat : ℤ) := by
          exact_mod_cast h_eq_nat
        rw [h_toNat1, h_toNat2] at h
        exact h
      linarith
    have hplane : data1.q 2 = data2.q 2 := by
      have h1 : data1.q 2 = (data1.k : ℝ) / 2 := data1.h_q2
      have h2 : data2.q 2 = (data2.k : ℝ) / 2 := data2.h_q2
      rw [h1, h2, h_k_eq]
    have h_hq0 : |(data1.q - data2.q) 0| ≤ δ / 100 := by
      have h_eq1 : q1 T1 = data1.q 0 := by unfold q1; rw [dif_pos hT1] <;> rfl
      have h_eq2 : q1 T2 = data2.q 0 := by unfold q1; rw [dif_pos hT2] <;> rfl
      have h : |q1 T1 - q1 T2| = |(data1.q - data2.q) 0| := by
        rw [h_eq1, h_eq2] <;> simp
      rw [h] at h_q1_close
      exact h_q1_close
    have h_hq1 : |(data1.q - data2.q) 1| ≤ δ / 100 := by
      have h_eq1 : q2 T1 = data1.q 1 := by unfold q2; rw [dif_pos hT1] <;> rfl
      have h_eq2 : q2 T2 = data2.q 1 := by unfold q2; rw [dif_pos hT2] <;> rfl
      have h : |q2 T1 - q2 T2| = |(data1.q - data2.q) 1| := by
        rw [h_eq1, h_eq2] <;> simp
      rw [h] at h_q2_close
      exact h_q2_close
    have h_htdiff : |data1.t0 - data2.t0| ≤ 1 / 8 := by
      have h_eq1 : t0 T1 = data1.t0 := by unfold t0; rw [dif_pos hT1] <;> rfl
      have h_eq2 : t0 T2 = data2.t0 := by unfold t0; rw [dif_pos hT2] <;> rfl
      have h : |t0 T1 - t0 T2| = |data1.t0 - data2.t0| := by rw [h_eq1, h_eq2]
      rw [h] at h_t0_close
      exact h_t0_close
    have h_hdir0 : |(data1.u' - data2.u') 0| ≤ δ / 100 := by
      have h_eq1 : du1 T1 = data1.u' 0 := by unfold du1; rw [dif_pos hT1] <;> rfl
      have h_eq2 : du1 T2 = data2.u' 0 := by unfold du1; rw [dif_pos hT2] <;> rfl
      have h : |du1 T1 - du1 T2| = |(data1.u' - data2.u') 0| := by
        rw [h_eq1, h_eq2] <;> simp
      rw [h] at h_du1_close
      exact h_du1_close
    have h_hdir1 : |(data1.u' - data2.u') 1| ≤ δ / 100 := by
      have h_eq1 : du2 T1 = data1.u' 1 := by unfold du2; rw [dif_pos hT1] <;> rfl
      have h_eq2 : du2 T2 = data2.u' 1 := by unfold du2; rw [dif_pos hT2] <;> rfl
      have h : |du2 T1 - du2 T2| = |(data1.u' - data2.u') 1| := by
        rw [h_eq1, h_eq2] <;> simp
      rw [h] at h_du2_close
      exact h_du2_close
    have h_hu2_1 : (u T1) 2 ≥ 1 / 2 := h_axis2_pos T1 hT1
    have h_hu2_2 : (u T2) 2 ≥ 1 / 2 := h_axis2_pos T2 hT2
    exact close_axial_tubes_not_distinct hδ hδ1
      frame (p T1) (u T1) (p T2) (u T2) data1.q data2.q data1.t0 data2.t0
      (h_p_eq T1 hT1) (h_u_eq T1 hT1) (h_p_eq T2 hT2) (h_u_eq T2 hT2)
      ⟨data1.h_t0_pos.le, data1.h_t0_le_one⟩
      ⟨data2.h_t0_pos.le, data2.h_t0_le_one⟩
      (by rw [data1.h_q_def, h_case1.1, h_case1.2] <;> ring)
      (by rw [data2.h_q_def, h_case2.1, h_case2.2] <;> ring)
      hplane h_hq0 h_hq1 h_htdiff
      (by rw [←h_case1.2, ←h_case2.2] <;> exact h_hdir0)
      (by rw [←h_case1.2, ←h_case2.2] <;> exact h_hdir1)
      h_hu2_1 h_hu2_2 h_capsule_lower h_capsule_upper
  have hR1 : 0 < P1 + D1 := by linarith
  have hR2 : 0 < P2 + D2 := by linarith
  exact phase_space_grid_packing_intercept hδ hδ1 hA hdistinct
    (P1 + D1) (P2 + D2) D1 D2
    hR1 hR2 hD1 hD2
    (2 * Nat.ceil A + 2)
    plane_idx q1 q2 t0 du1 du2
    h_plane h_q1_bound h_q2_bound h_t0_bound h_du1_bound h_du2_bound h_close

end Kakeya.Streamlined.GeometricLemmas
