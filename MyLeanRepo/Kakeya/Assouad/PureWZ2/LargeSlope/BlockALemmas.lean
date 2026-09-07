import MyLeanRepo.Kakeya.Assouad.LargeSlope.ProjectedNormalSlice
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedConvexOverload

/-!
# Block A helper lemmas: xz-projected normal convex overload
-/

noncomputable section

namespace Kakeya.Assouad

open scoped Classical

open Metric

/-- ‖xzProjectedNormal v‖² = v₀² + v₂². -/
lemma norm_xzProjectedNormal_sq (v : Point3) :
    ‖xzProjectedNormal v‖ ^ 2 = (v 0)^2 + (v 2)^2 := by
  have h1 : inner ℝ (xzProjectedNormal v) (xzProjectedNormal v) =
      ‖xzProjectedNormal v‖ ^ 2 := real_inner_self_eq_norm_sq (xzProjectedNormal v)
  have h2 : inner ℝ (xzProjectedNormal v) (xzProjectedNormal v) =
      (v 0)^2 + (v 2)^2 := by
    have h_sum : inner ℝ (xzProjectedNormal v) (xzProjectedNormal v) =
        inner ℝ (xzProjectedNormal v) (EuclideanSpace.single 0 (v 0)) +
        inner ℝ (xzProjectedNormal v) (EuclideanSpace.single 2 (v 2)) := by
      rw [xzProjectedNormal, inner_add_right]
    rw [h_sum]
    have h0 : inner ℝ (xzProjectedNormal v) (EuclideanSpace.single 0 (v 0)) = (v 0)^2 := by
      rw [EuclideanSpace.inner_single_right] <;> simp [xzProjectedNormal] <;> ring
    have h2 : inner ℝ (xzProjectedNormal v) (EuclideanSpace.single 2 (v 2)) = (v 2)^2 := by
      rw [EuclideanSpace.inner_single_right] <;> simp [xzProjectedNormal] <;> ring
    rw [h0, h2] <;> ring
  linarith

/-- normalizedXZNormal v has unit norm when xzProjectedNormal v is nonzero. -/
lemma normalizedXZNormal_unit {v : Point3} (h : 0 < ‖xzProjectedNormal v‖) :
    ‖normalizedXZNormal v‖ = 1 := by
  dsimp only [normalizedXZNormal]
  have h1 : ‖(‖xzProjectedNormal v‖⁻¹ • xzProjectedNormal v)‖ =
      |‖xzProjectedNormal v‖⁻¹| * ‖xzProjectedNormal v‖ := norm_smul _ _
  rw [h1]
  have h2 : |‖xzProjectedNormal v‖⁻¹| = ‖xzProjectedNormal v‖⁻¹ := by
    rw [abs_of_pos] <;> positivity
  rw [h2]
  field_simp [h.ne'] <;> ring

/-- Lemma A: If ‖v‖ = 1 and |v_y| ≤ 1/2, then normalizedXZNormal v has unit norm. -/
lemma normalizedXZNormal_unit_of_y_bound {v : Point3}
    (hv_unit : ‖v‖ = 1) (hvy : |v (1 : Fin 3)| ≤ 1 / 2) :
    ‖normalizedXZNormal v‖ = 1 := by
  have hvy2 : (v 1)^2 ≤ 1 / 4 := by
    have h1 : -(1 / 2 : ℝ) ≤ v 1 := (abs_le.mp hvy).1
    have h2 : v 1 ≤ (1 / 2 : ℝ) := (abs_le.mp hvy).2
    have h3 : (v 1)^2 ≤ (1 / 2 : ℝ)^2 := by nlinarith
    norm_num at h3 ⊢ <;> exact h3
  have hsum : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    have h : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have h3 : inner ℝ v v = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
      simp [inner, Fin.sum_univ_succ] <;> ring
    linarith
  have h4 : (v 0)^2 + (v 2)^2 ≥ 3 / 4 := by
    have h5 : ‖v‖ ^ 2 = 1 := by rw [hv_unit] <;> norm_num
    linarith [hsum, h5, hvy2]
  have h6 : ‖xzProjectedNormal v‖ ^ 2 = (v 0)^2 + (v 2)^2 :=
    norm_xzProjectedNormal_sq v
  have h7 : ‖xzProjectedNormal v‖ ^ 2 ≥ 3 / 4 := by
    calc ‖xzProjectedNormal v‖ ^ 2
      = (v 0)^2 + (v 2)^2 := h6
    _ ≥ 3 / 4 := h4
  have h_nonneg : 0 ≤ ‖xzProjectedNormal v‖ := by positivity
  have h8 : 0 < ‖xzProjectedNormal v‖ := by
    by_cases h9 : ‖xzProjectedNormal v‖ = 0
    · rw [h9] at h7 <;> norm_num at h7
    · exact lt_of_le_of_ne h_nonneg (Ne.symm h9)
  exact normalizedXZNormal_unit h8

/-- Lemma A (alternative): from 1/2 ≤ ‖xzProjectedNormal v‖. -/
lemma normalizedXZNormal_unit_of_proj_lower {v : Point3}
    (h : (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖) :
    ‖normalizedXZNormal v‖ = 1 := by
  have hpos : 0 < ‖xzProjectedNormal v‖ := by linarith
  exact normalizedXZNormal_unit hpos

/-- ‖xzProjectedNormal v‖ ≤ ‖v‖. -/
lemma norm_xzProjected_le_norm (v : Point3) :
    ‖xzProjectedNormal v‖ ≤ ‖v‖ := by
  have h1 : ‖xzProjectedNormal v‖ ^ 2 = (v 0)^2 + (v 2)^2 :=
    norm_xzProjectedNormal_sq v
  have h2 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    have h : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have h3 : inner ℝ v v = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
      simp [inner, Fin.sum_univ_succ] <;> ring
    linarith
  have h4 : ‖xzProjectedNormal v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    calc ‖xzProjectedNormal v‖ ^ 2
      = (v 0)^2 + (v 2)^2 := h1
    _ ≤ (v 0)^2 + (v 1)^2 + (v 2)^2 := by nlinarith [sq_nonneg (v 1)]
    _ = ‖v‖ ^ 2 := h2.symm
  have h5 : 0 ≤ ‖xzProjectedNormal v‖ := by positivity
  have h6 : 0 ≤ ‖v‖ := by positivity
  nlinarith

/-- AD transfers from v to xzProjectedNormal v on a fixed y-slice. -/
lemma ad_transfer_xz_projected_on_slice
    {E : Set Point3} {v : Point3} {y₀ rho alpha : ℝ} {C : ENNReal}
    (hv_unit : ‖v‖ = 1)
    (hE_bounded : E ⊆ Kakeya.DeltaTube.unitBall)
    (hE_slice : ∀ p ∈ E, p (1 : Fin 3) = y₀)
    (hAD : IsADSet1 (scalarProjection v E) rho alpha C) :
    IsADSet1 (scalarProjection (xzProjectedNormal v) E) rho alpha C :=
  (large_slope_projected_normal_slice E v y₀ rho alpha C hv_unit
    hE_bounded hE_slice).2 hAD

/--
Lemma B: AD transfer to normalizedXZNormal on a y-slice via dilation.
Output base scale is s*rho where s = ‖xzProjectedNormal v‖⁻¹ ≥ 1.
-/
lemma ad_transfer_to_normalized_xz
    {E : Set Point3} {v : Point3} {y₀ rho alpha : ℝ} {C : ENNReal}
    (hv_unit : ‖v‖ = 1)
    (hE_bounded : E ⊆ Kakeya.DeltaTube.unitBall)
    (hE_slice : ∀ p ∈ E, p (1 : Fin 3) = y₀)
    (hAD : IsADSet1 (scalarProjection v E) rho alpha C)
    (h_proj_lower : (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖)
    (h_dilated_bounded :
      (fun x : ℝ => ‖xzProjectedNormal v‖⁻¹ * x) ''
        scalarProjection (xzProjectedNormal v) E ⊆ Set.Icc (-4 : ℝ) 4)
    (h_scale_le_one : ‖xzProjectedNormal v‖⁻¹ * rho ≤ 1) :
    IsADSet1 (scalarProjection (normalizedXZNormal v) E)
      (‖xzProjectedNormal v‖⁻¹ * rho) alpha C := by
  set s : ℝ := ‖xzProjectedNormal v‖⁻¹ with hs_def
  have hpos : 0 < ‖xzProjectedNormal v‖ := by linarith
  have h1 : ‖xzProjectedNormal v‖ ≤ 1 := by
    have h2 : ‖xzProjectedNormal v‖ ≤ ‖v‖ := norm_xzProjected_le_norm v
    rw [hv_unit] at h2
    exact h2
  have hs_ge_one : 1 ≤ s := by
    have h3 : 0 < ‖xzProjectedNormal v‖ := hpos
    have h4 : s * ‖xzProjectedNormal v‖ = 1 := by
      simp [hs_def, h3.ne'] <;> field_simp [h3.ne'] <;> ring
    nlinarith
  have hAD_xz : IsADSet1 (scalarProjection (xzProjectedNormal v) E) rho alpha C :=
    ad_transfer_xz_projected_on_slice hv_unit hE_bounded hE_slice hAD
  let E_xz : Set ℝ := scalarProjection (xzProjectedNormal v) E
  have h_def_norm : normalizedXZNormal v = s • xzProjectedNormal v := by
    simp [normalizedXZNormal, hs_def]
  have h_smul_eq : ∀ p, inner ℝ p (normalizedXZNormal v) = s * inner ℝ p (xzProjectedNormal v) := by
    intro p
    rw [h_def_norm, inner_smul_right] <;> ring
  have h_eq : scalarProjection (normalizedXZNormal v) E = (fun x : ℝ => s * x) '' E_xz := by
    ext t
    simp only [E_xz, Set.mem_image, scalarProjection]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨inner ℝ p (xzProjectedNormal v), ?_, ?_⟩
      · exact ⟨p, hp, rfl⟩
      · exact (h_smul_eq p).symm
    · rintro ⟨t', ⟨p, hp, h_eq1⟩, h_eq2⟩
      have h3 : inner ℝ p (normalizedXZNormal v) = t := by
        calc inner ℝ p (normalizedXZNormal v)
          = s * inner ℝ p (xzProjectedNormal v) := h_smul_eq p
        _ = s * t' := by rw [h_eq1]
        _ = t := h_eq2
      exact ⟨p, hp, h3⟩
  rw [h_eq]
  have hC_one : 1 ≤ C := hAD.2.2.2.1
  exact IsADSet1.dilation_ge_one hs_ge_one hAD_xz h_dilated_bounded h_scale_le_one
    hAD.1 hAD.2.1 hAD.2.2.1 hC_one

/--
Lemma C: Direction bound for normalized xz-projected normal.
Caller supplies the instantiated direction bound function.
-/
lemma direction_bound_normalized_xz
    {delta rho sigma eta : ℝ}
    {C : ENNReal}
    {E : Set Point3}
    {base direction v : Point3}
    {start : ℝ}
    (hdelta : 0 < delta)
    (hrho_pos : 0 < rho)
    (h_proj_lower : (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖)
    (hE_sub : E ⊆ tubeSegmentCarrier (6 * delta) base direction start
        (‖xzProjectedNormal v‖⁻¹ * rho))
    (hvol : ENNReal.ofReal
        (36 * Real.rpow delta eta * delta^2 *
          Real.sqrt (‖xzProjectedNormal v‖⁻¹ * rho)) ≤
      MeasureTheory.volume E)
    (hAD_normalized : IsADSet1
        (scalarProjection (normalizedXZNormal v) E)
        (‖xzProjectedNormal v‖⁻¹ * rho) (1 - sigma) C)
    (h6delta : 6 * delta ≤ ‖xzProjectedNormal v‖⁻¹ * rho)
    (hrho_le_quarter : ‖xzProjectedNormal v‖⁻¹ * rho ≤ 1 / 4)
    (hdir_unit : ‖direction‖ = 1)
    (hE_meas : MeasurableSet E)
    (hdelta_le_one : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (heta : 0 < eta)
    (hdir_bound : ∀ (rho' start' : ℝ), 0 < delta → delta ≤ 1 →
        6 * delta ≤ rho' → rho' ≤ 1 / 4 →
        ∀ (base' direction' v' : Point3),
          ‖direction'‖ = 1 → ‖v'‖ = 1 →
          ∀ (E' : Set Point3), MeasurableSet E' →
            E' ⊆ tubeSegmentCarrier (6 * delta) base' direction' start' rho' →
            ENNReal.ofReal (36 * Real.rpow delta eta * delta^2 * Real.sqrt rho') ≤
              MeasureTheory.volume E' →
            IsADSet1 (scalarProjection v' E') rho' (1 - sigma) C →
            ENNReal.ofReal (|inner ℝ direction' v'| / Real.sqrt rho') ≤
              Kakeya.realRpowENN delta (-(3 * eta / sigma))) :
    |inner ℝ direction (normalizedXZNormal v)| ≤
        Real.sqrt (‖xzProjectedNormal v‖⁻¹ * rho) *
        Real.rpow delta (-(3 * eta / sigma)) := by
  set s : ℝ := ‖xzProjectedNormal v‖⁻¹ with hs_def
  set rho' : ℝ := s * rho with hrho'_def
  have hpos : 0 < ‖xzProjectedNormal v‖ := by linarith
  have h_nunit : ‖normalizedXZNormal v‖ = 1 :=
    normalizedXZNormal_unit_of_proj_lower h_proj_lower
  have hs_pos : 0 < s := by positivity
  have hrho'_pos : 0 < rho' := mul_pos hs_pos hrho_pos
  have hsqrt_pos : 0 < Real.sqrt rho' := Real.sqrt_pos.mpr hrho'_pos
  have h_result : ENNReal.ofReal (|inner ℝ direction (normalizedXZNormal v)| / Real.sqrt rho') ≤
      Kakeya.realRpowENN delta (-(3 * eta / sigma)) :=
    hdir_bound rho' start hdelta hdelta_le_one h6delta hrho_le_quarter
      base direction (normalizedXZNormal v) hdir_unit h_nunit
      E hE_meas hE_sub hvol hAD_normalized
  set x : ℝ := |inner ℝ direction (normalizedXZNormal v)| / Real.sqrt rho' with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have h_rpow_nonneg : 0 ≤ Real.rpow delta (-(3 * eta / sigma)) := by
    apply Real.rpow_nonneg
    positivity
  have h11 : x ≤ Real.rpow delta (-(3 * eta / sigma)) := by
    have h_rpow : Kakeya.realRpowENN delta (-(3 * eta / sigma)) =
        ENNReal.ofReal (Real.rpow delta (-(3 * eta / sigma))) := by
      simp [Kakeya.realRpowENN]
    rw [h_rpow] at h_result
    exact (ENNReal.ofReal_le_ofReal_iff h_rpow_nonneg).mp h_result
  have h12 : |inner ℝ direction (normalizedXZNormal v)| ≤
      Real.sqrt rho' * Real.rpow delta (-(3 * eta / sigma)) := by
    have h13 : |inner ℝ direction (normalizedXZNormal v)| = x * Real.sqrt rho' := by
      simp [hx_def, hsqrt_pos.ne'] <;> field_simp [hsqrt_pos.ne'] <;> ring
    rw [h13]
    have h14 : 0 ≤ Real.sqrt rho' := by positivity
    have h15 : x * Real.sqrt rho' ≤ Real.rpow delta (-(3 * eta / sigma)) * Real.sqrt rho' :=
      mul_le_mul_of_nonneg_right h11 h14
    linarith
  simpa [hrho'_def] using h12

/-- The y-component of xzProjectedNormal v is zero. -/
lemma xzProjectedNormal_y_zero (v : Point3) :
    (xzProjectedNormal v) (1 : Fin 3) = 0 := by
  simp [xzProjectedNormal]

/--
Key identity: inner(p, xzProjectedNormal v) = inner(p, v) - p 1 * v 1.

On a fixed y-slice p 1 = y₀, this differs from inner(p, v) by a constant,
which is why AD transfers via translation.
-/
lemma inner_xzProjectedNormal (p v : Point3) :
    inner ℝ p (xzProjectedNormal v) = inner ℝ p v - p (1 : Fin 3) * v (1 : Fin 3) := by
  have h_sum : ∀ (q : Point3), inner ℝ p q = ∑ i : Fin 3, p i * q i := by
    intro q
    simp [inner, Fin.sum_univ_succ] <;> ring
  rw [h_sum (xzProjectedNormal v), h_sum v]
  have h_xz : ∑ i : Fin 3, p i * (xzProjectedNormal v) i =
      p 0 * v 0 + p 2 * v 2 := by
    simp [xzProjectedNormal, Fin.sum_univ_succ] <;> ring
  have h_v : ∑ i : Fin 3, p i * v i = p 0 * v 0 + p 1 * v 1 + p 2 * v 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  rw [h_xz, h_v] <;> ring

/--
Slab containment with the xz-projected normal.

Given a direction bound K for the normalized xz-projected normal, the tube
carrier is contained in an oriented box slab of width 2√3·K + 12δ.

This is just `paper_tube_contained_in_box_slab` applied to
`normalizedXZNormal v`, but stated explicitly for the Block A workflow.
-/
lemma xz_projected_slab_containment
    {delta : ℝ} (hdelta : 0 < delta)
    {T : Kakeya.DeltaTube delta}
    {v : Point3} {q : Point3}
    (h_proj_lower : (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖)
    (hq : q ∈ wz1PaperTubeCarrier T)
    (K : ℝ) (hK_nonneg : 0 ≤ K)
    (hdir_bound : |inner ℝ T.direction (normalizedXZNormal v)| ≤ K) :
    wz1PaperTubeCarrier T ⊆
      orientedBoxSlab q (normalizedXZNormal v)
        (2 * Real.sqrt 3 * K + 12 * delta) := by
  have h_nunit : ‖normalizedXZNormal v‖ = 1 :=
    normalizedXZNormal_unit_of_proj_lower h_proj_lower
  exact paper_tube_contained_in_box_slab hdelta hK_nonneg
    (normalizedXZNormal v) q h_nunit hq hdir_bound

/--
A half-open square in the xz-plane with side length r.
-/
def xzGridSquare (r x₀ z₀ : ℝ) (k l : ℤ) : Set (ℝ × ℝ) :=
  Set.Ico (x₀ + (k : ℝ) * r) (x₀ + ((k : ℝ) + 1) * r) ×ˢ
  Set.Ico (z₀ + (l : ℝ) * r) (z₀ + ((l : ℝ) + 1) * r)

/-- Helper: if a finset of integers has card ≥ 3, it has two elements differing by ≥ 2. -/
private lemma finset_int_three_gap (s : Finset ℤ) (h : 3 ≤ s.card) :
    ∃ (a b : ℤ), a ∈ s ∧ b ∈ s ∧ 2 ≤ b - a := by
  have hne : s.Nonempty := Finset.card_pos.mp (by linarith)
  let a := s.min' hne
  let b := s.max' hne
  have ha : a ∈ s := Finset.min'_mem s hne
  have hb : b ∈ s := Finset.max'_mem s hne
  have hdiff : 2 ≤ b - a := by
    by_contra h'
    have h'' : b - a ≤ 1 := by linarith
    have hsub : s ⊆ Finset.Icc a (a + 1) := by
      intro k hk
      have h1 : a ≤ k := Finset.min'_le s k hk
      have h2 : k ≤ b := Finset.le_max' s k hk
      exact Finset.mem_Icc.mpr ⟨h1, by linarith⟩
    have hcard : s.card ≤ (Finset.Icc a (a + 1)).card := Finset.card_le_card hsub
    have h2card : (Finset.Icc a (a + 1)).card = 2 := by
      simp [Finset.Icc_eq_empty_of_lt]
      <;> omega
    rw [h2card] at hcard
    linarith
  exact ⟨a, b, ha, hb, hdiff⟩

/--
A set with x-diameter < r and z-diameter < r intersects at most 4 grid squares
of side length r (at most 2 in each coordinate).

This is the √ρ-grid incidence bound for the Block A square pigeonhole.
-/
lemma small_set_meets_at_most_four_squares
    {r : ℝ} (hr : 0 < r)
    {x₀ z₀ : ℝ}
    {A : Set (ℝ × ℝ)}
    (hx_diam : ∀ (p q : ℝ × ℝ), p ∈ A → q ∈ A → |p.1 - q.1| < r)
    (hz_diam : ∀ (p q : ℝ × ℝ), p ∈ A → q ∈ A → |p.2 - q.2| < r)
    (indices : Finset (ℤ × ℤ)) :
    (indices.filter (fun kl : ℤ × ℤ => (A ∩ xzGridSquare r x₀ z₀ kl.1 kl.2).Nonempty)).card ≤ 4 := by
  classical
  let P : (ℤ × ℤ) → Prop := fun kl => (A ∩ xzGridSquare r x₀ z₀ kl.1 kl.2).Nonempty
  let S : Finset (ℤ × ℤ) := indices.filter P
  let ks : Finset ℤ := S.image Prod.fst
  let ls : Finset ℤ := S.image Prod.snd
  have h_k_le : ks.card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ ks.card := by linarith
    rcases finset_int_three_gap ks h3 with ⟨kmin, kmax, hkmin, hkmax, hdiff⟩
    have h1 : ∃ (kl : ℤ × ℤ), kl ∈ S ∧ kl.1 = kmin := by
      simpa [ks, Finset.mem_image] using hkmin
    have h2 : ∃ (kl : ℤ × ℤ), kl ∈ S ∧ kl.1 = kmax := by
      simpa [ks, Finset.mem_image] using hkmax
    rcases h1 with ⟨kl1, hkl1, h_eq1⟩
    rcases h2 with ⟨kl2, hkl2, h_eq2⟩
    have hP1 : P kl1 := (Finset.mem_filter.mp hkl1).2
    have hP2 : P kl2 := (Finset.mem_filter.mp hkl2).2
    rcases hP1 with ⟨p, hpA, hpSq⟩
    rcases hP2 with ⟨q, hqA, hqSq⟩
    have h_p_x_upper : p.1 < x₀ + ((kmin : ℝ) + 1) * r := by
      have h : p.1 < x₀ + ((kl1.1 : ℝ) + 1) * r := hpSq.1.2
      rw [show (kl1.1 : ℝ) = (kmin : ℝ) from by exact_mod_cast h_eq1] at h
      exact h
    have h_q_x_lower : x₀ + (kmax : ℝ) * r ≤ q.1 := by
      have h : x₀ + (kl2.1 : ℝ) * r ≤ q.1 := hqSq.1.1
      rw [show (kl2.1 : ℝ) = (kmax : ℝ) from by exact_mod_cast h_eq2] at h
      exact h
    have h_kmax_ge : (kmax : ℝ) - (kmin : ℝ) ≥ 2 := by exact_mod_cast hdiff
    have h_main : q.1 - p.1 > r := by
      have h1 : q.1 - p.1 > ((kmax : ℝ) - (kmin : ℝ) - 1) * r := by
        calc q.1 - p.1
          ≥ x₀ + (kmax : ℝ) * r - p.1 := by linarith
        _ > x₀ + (kmax : ℝ) * r - (x₀ + ((kmin : ℝ) + 1) * r) := by linarith
        _ = ((kmax : ℝ) - (kmin : ℝ) - 1) * r := by ring
      have h2 : ((kmax : ℝ) - (kmin : ℝ) - 1) * r ≥ r := by
        have h3 : (kmax : ℝ) - (kmin : ℝ) - 1 ≥ 1 := by linarith
        have h4 : 0 ≤ r := by linarith
        nlinarith
      linarith
    have h_ge : |q.1 - p.1| ≥ r := by
      have h_pos : 0 < q.1 - p.1 := by linarith [hr]
      have h_abs : |q.1 - p.1| = q.1 - p.1 := abs_of_pos h_pos
      rw [h_abs]
      exact h_main.le
    have h_lt : |q.1 - p.1| < r := hx_diam q p hqA hpA
    exact absurd h_lt (not_lt.mpr h_ge)
  have h_l_le : ls.card ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ ls.card := by linarith
    rcases finset_int_three_gap ls h3 with ⟨lmin, lmax, hlmin, hlmax, hdiff⟩
    have h1 : ∃ (kl : ℤ × ℤ), kl ∈ S ∧ kl.2 = lmin := by
      simpa [ls, Finset.mem_image] using hlmin
    have h2 : ∃ (kl : ℤ × ℤ), kl ∈ S ∧ kl.2 = lmax := by
      simpa [ls, Finset.mem_image] using hlmax
    rcases h1 with ⟨kl1, hkl1, h_eq1⟩
    rcases h2 with ⟨kl2, hkl2, h_eq2⟩
    have hP1 : P kl1 := (Finset.mem_filter.mp hkl1).2
    have hP2 : P kl2 := (Finset.mem_filter.mp hkl2).2
    rcases hP1 with ⟨p, hpA, hpSq⟩
    rcases hP2 with ⟨q, hqA, hqSq⟩
    have h_p_z_upper : p.2 < z₀ + ((lmin : ℝ) + 1) * r := by
      have h : p.2 < z₀ + ((kl1.2 : ℝ) + 1) * r := hpSq.2.2
      rw [show (kl1.2 : ℝ) = (lmin : ℝ) from by exact_mod_cast h_eq1] at h
      exact h
    have h_q_z_lower : z₀ + (lmax : ℝ) * r ≤ q.2 := by
      have h : z₀ + (kl2.2 : ℝ) * r ≤ q.2 := hqSq.2.1
      rw [show (kl2.2 : ℝ) = (lmax : ℝ) from by exact_mod_cast h_eq2] at h
      exact h
    have h_lmax_ge : (lmax : ℝ) - (lmin : ℝ) ≥ 2 := by exact_mod_cast hdiff
    have h_main : q.2 - p.2 > r := by
      have h1 : q.2 - p.2 > ((lmax : ℝ) - (lmin : ℝ) - 1) * r := by
        calc q.2 - p.2
          ≥ z₀ + (lmax : ℝ) * r - p.2 := by linarith
        _ > z₀ + (lmax : ℝ) * r - (z₀ + ((lmin : ℝ) + 1) * r) := by linarith
        _ = ((lmax : ℝ) - (lmin : ℝ) - 1) * r := by ring
      have h2 : ((lmax : ℝ) - (lmin : ℝ) - 1) * r ≥ r := by
        have h3 : (lmax : ℝ) - (lmin : ℝ) - 1 ≥ 1 := by linarith
        have h4 : 0 ≤ r := by linarith
        nlinarith
      linarith
    have h_ge : |q.2 - p.2| ≥ r := by
      have h_pos : 0 < q.2 - p.2 := by linarith [hr]
      have h_abs : |q.2 - p.2| = q.2 - p.2 := abs_of_pos h_pos
      rw [h_abs]
      exact h_main.le
    have h_lt : |q.2 - p.2| < r := hz_diam q p hqA hpA
    exact absurd h_lt (not_lt.mpr h_ge)
  have hS_subset : S ⊆ ks ×ˢ ls := by
    intro kl h
    have h1 : kl.1 ∈ ks := Finset.mem_image.mpr ⟨kl, h, rfl⟩
    have h2 : kl.2 ∈ ls := Finset.mem_image.mpr ⟨kl, h, rfl⟩
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have h_card : S.card ≤ (ks ×ˢ ls).card := Finset.card_le_card hS_subset
  have h_prod : (ks ×ˢ ls).card = ks.card * ls.card := by
    exact Finset.card_product ks ls
  rw [h_prod] at h_card
  have h_final : ks.card * ls.card ≤ 4 := by
    have h1 : ks.card ≤ 2 := h_k_le
    have h2 : ls.card ≤ 2 := h_l_le
    have h3 : ks.card * ls.card ≤ 2 * 2 := by gcongr <;> omega
    norm_num at h3 ⊢ <;> exact h3
  exact h_card.trans h_final

/--
Center shift bound for a normal with y=0, when both points are in the same xzGridPrism.

Since the normal has no y-component, the inner product only depends on x and z differences,
which are both bounded by the prism side length `b-a`.
-/
lemma prism_center_shift_y_zero_normal
    {x₀ a b : ℝ} {k : ℤ} {p c : Point3} {n : Point3}
    (hba : 0 < b - a)
    (hp : p ∈ xzGridPrism x₀ a b k)
    (hc : c ∈ xzGridPrism x₀ a b k)
    (hn_y : n 1 = 0)
    (hn_unit : ‖n‖ = 1) :
    |inner ℝ (p - c) n| ≤ Real.sqrt 2 * (b - a) := by
  have hx : |p 0 - c 0| ≤ b - a := by
    have h11 : x₀ + (k : ℝ) * (b - a) ≤ p 0 := hp.1.1
    have h12 : p 0 < x₀ + ((k : ℝ) + 1) * (b - a) := hp.1.2
    have h21 : x₀ + (k : ℝ) * (b - a) ≤ c 0 := hc.1.1
    have h22 : c 0 < x₀ + ((k : ℝ) + 1) * (b - a) := hc.1.2
    have h_upper : p 0 - c 0 < b - a := by linarith
    have h_lower : -(b - a) < p 0 - c 0 := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hz : |p 2 - c 2| ≤ b - a := by
    have h11 : a ≤ p 2 := hp.2.1
    have h12 : p 2 ≤ b := hp.2.2
    have h21 : a ≤ c 2 := hc.2.1
    have h22 : c 2 ≤ b := hc.2.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hinner : inner ℝ (p - c) n = (p 0 - c 0) * n 0 + (p 2 - c 2) * n 2 := by
    have h1 : inner ℝ (p - c) n = (p - c) 0 * n 0 + (p - c) 1 * n 1 + (p - c) 2 * n 2 := by
      simp [inner, Fin.sum_univ_succ] <;> ring
    rw [h1]
    have h2 : (p - c) 1 * n 1 = 0 := by
      have h3 : n 1 = 0 := hn_y
      rw [h3] <;> ring
    have h4 : (p - c) 0 = p 0 - c 0 := by simp
    have h5 : (p - c) 2 = p 2 - c 2 := by simp
    rw [h2, h4, h5] <;> ring
  rw [hinner]
  have h6 : |(p 0 - c 0) * n 0 + (p 2 - c 2) * n 2| ≤
      |p 0 - c 0| * |n 0| + |p 2 - c 2| * |n 2| := by
    calc
      |(p 0 - c 0) * n 0 + (p 2 - c 2) * n 2|
        ≤ |(p 0 - c 0) * n 0| + |(p 2 - c 2) * n 2| := abs_add_le _ _
      _ = |p 0 - c 0| * |n 0| + |p 2 - c 2| * |n 2| := by
        rw [abs_mul, abs_mul] <;> ring
  have h7 : |n 0| + |n 2| ≤ Real.sqrt 2 := by
    have h_sum_sq : (n 0)^2 + (n 2)^2 = 1 := by
      have h1 : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
      have h2 : inner ℝ n n = (n 0)^2 + (n 1)^2 + (n 2)^2 := by
        simp [inner, Fin.sum_univ_succ] <;> ring
      have h3 : ‖n‖ ^ 2 = 1 := by rw [hn_unit] <;> norm_num
      have h4 : (n 1)^2 = 0 := by rw [hn_y] <;> ring
      linarith
    have h5 : (|n 0| + |n 2|) ^ 2 ≤ 2 := by
      have h6 : (|n 0| + |n 2|) ^ 2 = |n 0|^2 + |n 2|^2 + 2 * |n 0| * |n 2| := by ring
      rw [h6]
      have h71 : |n 0|^2 = (n 0)^2 := by rw [sq_abs]
      have h72 : |n 2|^2 = (n 2)^2 := by rw [sq_abs]
      rw [h71, h72]
      have h9 : 2 * |n 0| * |n 2| ≤ (n 0)^2 + (n 2)^2 := by
        nlinarith [sq_nonneg (|n 0| - |n 2|)]
      nlinarith
    have h10 : 0 ≤ |n 0| + |n 2| := by positivity
    have h11 : |n 0| + |n 2| ≤ Real.sqrt 2 := by
      calc
        |n 0| + |n 2|
          = Real.sqrt ((|n 0| + |n 2|) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg h10]
        _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h5
    exact h11
  calc
    |(p 0 - c 0) * n 0 + (p 2 - c 2) * n 2|
      ≤ |p 0 - c 0| * |n 0| + |p 2 - c 2| * |n 2| := h6
    _ ≤ (b - a) * |n 0| + (b - a) * |n 2| := by gcongr <;> linarith
    _ = (b - a) * (|n 0| + |n 2|) := by ring
    _ ≤ (b - a) * Real.sqrt 2 := by gcongr
    _ = Real.sqrt 2 * (b - a) := by ring

/-- normalizedXZNormal v has y-component zero. -/
lemma normalizedXZNormal_y_zero (v : Point3) : (normalizedXZNormal v) 1 = 0 := by
  simp [normalizedXZNormal, xzProjectedNormal]

end Kakeya.Assouad

end
