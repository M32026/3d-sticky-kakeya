import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicProjectionIdentity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Global AD transfer under anisotropic rescaling

Using the exact projection identity, transfer `PureWZ2PaperADSet1` from the
old slope `g` to the rescaled slope `f`. Since the projected sets are exactly
equal, only base-scale weakening and constant absorption are needed.

Also includes subset monotonicity, which handles the case where the rescaled
shading is a subset of the exact image (e.g. via cubicalization).
-/

noncomputable section

namespace Kakeya.Assouad

variable (g : SlopeFunction) (c d m : ℝ)

/-- Weaken the base scale of `PureWZ2PaperADSet1`. -/
lemma PureWZ2PaperADSet1.weaken_scale
    {S : Set ℝ} {delta rho alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (hrho : 0 < rho) (hdelta_le_rho : delta ≤ rho) :
    PureWZ2PaperADSet1 S rho alpha C := by
  rcases hAD with ⟨hdelta, halpha, halpha1, hC, hC_top, hcover⟩
  refine ⟨hrho, halpha, halpha1, hC, hC_top, ?_⟩
  intro rho' hrho' hrho_le left length hlength
  have hdelta_le_rho' : delta ≤ rho' := le_trans hdelta_le_rho hrho_le
  exact hcover rho' hrho' hdelta_le_rho' left length hlength

/-- Weaken the constant of `PureWZ2PaperADSet1`. -/
lemma PureWZ2PaperADSet1.weaken_constant
    {S : Set ℝ} {delta alpha : ℝ} {C C' : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (hC_le : C ≤ C') (hC'_one : 1 ≤ C') (hC'_top : C' ≠ ⊤) :
    PureWZ2PaperADSet1 S delta alpha C' := by
  rcases hAD with ⟨hdelta, halpha, halpha1, hC, hC_top, hcover⟩
  refine ⟨hdelta, halpha, halpha1, hC'_one, hC'_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  have h := hcover rho hrho hdelta_rho left length hlength
  have h' : C * Kakeya.realRpowENN (length / rho) alpha ≤
        C' * Kakeya.realRpowENN (length / rho) alpha := by
    gcongr
  exact h.trans h'

/--
Transfer global AD from old slope `g` to rescaled slope `f` for the EXACT image.

The projection sets are exactly equal, so only scale weakening and constant
absorption are needed.
-/
lemma pureWZ2_anisotropic_ad_transfer
    {E : Set Point3}
    {delta rho sigma loss : ℝ} {C : ENNReal}
    (hcd : c < d) (hm : 0 < m)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hdelta_le_rho : delta ≤ rho)
    (hsigma : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hloss : 0 < loss)
    (hC : 1 ≤ C) (hC_top : C ≠ ⊤)
    (h_const : C ≤ Kakeya.realRpowENN rho (-loss))
    (h_old : ∀ z ∈ Set.Icc c d,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (g z))
          (horizontalSlice E z))
        delta (1 - sigma) C) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (anisotropicRescaledSlope g c d m t))
          (horizontalSlice (anisotropicRescalingMap g c d m '' E) t))
        rho (1 - sigma) (Kakeya.realRpowENN rho (-loss)) := by
  intro t ht
  rcases ht with ⟨ht1, ht2⟩
  set z : ℝ := c + (d - c) / 2 * (t + 1) with hz_def
  have hz_in : z ∈ Set.Icc c d := by
    have h_h_pos : 0 < d - c := by linarith
    have h_t1 : 0 ≤ t + 1 := by linarith
    have h_t2 : t + 1 ≤ 2 := by linarith
    have h1 : c ≤ z := by
      rw [hz_def]
      have h3 : 0 ≤ (d - c) / 2 * (t + 1) := by positivity
      linarith
    have h2 : z ≤ d := by
      rw [hz_def]
      have h4 : (d - c) / 2 * (t + 1) ≤ d - c := by
        calc
          (d - c) / 2 * (t + 1) ≤ (d - c) / 2 * 2 := by gcongr
          _ = d - c := by ring
      linarith
    exact ⟨h1, h2⟩
  have h_id :
      scalarProjection (globalGrainDirection (anisotropicRescaledSlope g c d m t))
        (horizontalSlice (anisotropicRescalingMap g c d m '' E) t) =
      scalarProjection (globalGrainDirection (g z))
        (horizontalSlice E z) :=
    anisotropic_projection_set g c d m hcd hm E t
  have h_old_ad : PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (g z))
          (horizontalSlice E z))
        delta (1 - sigma) C := h_old z hz_in
  rw [h_id]
  have h1 : PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (g z))
          (horizontalSlice E z))
        rho (1 - sigma) C :=
    h_old_ad.weaken_scale hrho hdelta_le_rho
  have h_rpow_one : (1 : ENNReal) ≤ Kakeya.realRpowENN rho (-loss) := by
    have h1 : (1 : ℝ) ≤ Real.rpow rho (-loss) := by
      have h2 : Real.rpow rho 0 ≤ Real.rpow rho (-loss) :=
        Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
      have h3 : Real.rpow rho 0 = 1 := by exact Real.rpow_zero rho
      rw [h3] at h2
      exact h2
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h1
  have h_rpow_top : Kakeya.realRpowENN rho (-loss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  exact h1.weaken_constant h_const h_rpow_one h_rpow_top

/-- AD is monotone under subsets: a subset of an AD set has the same AD bound. -/
lemma PureWZ2PaperADSet1.weaken_subset
    {T S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (hT : T ⊆ S) :
    PureWZ2PaperADSet1 T delta alpha C := by
  rcases hAD with ⟨hdelta, halpha, halpha1, hC, hC_top, hcover⟩
  refine ⟨hdelta, halpha, halpha1, hC, hC_top, ?_⟩
  intro rho hrho hdelta_rho left length hlength
  have h1 : T ∩ Set.Icc left (left + length) ⊆
      S ∩ Set.Icc left (left + length) :=
    Set.inter_subset_inter hT (Set.Subset.refl _)
  have h2 : Metric.externalCoveringNumber ⟨rho, hrho⟩
        (T ∩ Set.Icc left (left + length)) ≤
      Metric.externalCoveringNumber ⟨rho, hrho⟩
        (S ∩ Set.Icc left (left + length)) :=
    Metric.externalCoveringNumber_mono_set h1
  have h3 := hcover rho hrho hdelta_rho left length hlength
  exact le_trans (mod_cast h2) h3

/--
Simplified global AD transfer when the rescaled shading `Y'` is a SUBSET of
the exact anisotropic image `Φ '' E`.

Since AD is monotone under subsets and the exact image has AD with constant
`rho^(-loss)`, any subset inherits the same bound with NO constant blowup.

This is the preferred path when the cubicalization produces shading carriers
contained in the exact image.
-/
lemma pureWZ2_anisotropic_ad_transfer_subset
    {E Y' : Set Point3}
    {delta rho sigma loss : ℝ} {C : ENNReal}
    (hcd : c < d) (hm : 0 < m)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (hdelta_le_rho : delta ≤ rho)
    (hsigma : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hloss : 0 < loss)
    (hC : 1 ≤ C) (hC_top : C ≠ ⊤)
    (h_const : C ≤ Kakeya.realRpowENN rho (-loss))
    (h_old : ∀ z ∈ Set.Icc c d,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (g z))
          (horizontalSlice E z))
        delta (1 - sigma) C)
    (hY' : Y' ⊆ anisotropicRescalingMap g c d m '' E) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (anisotropicRescaledSlope g c d m t))
          (horizontalSlice Y' t))
        rho (1 - sigma) (Kakeya.realRpowENN rho (-loss)) := by
  intro t ht
  set v : Point3 := globalGrainDirection (anisotropicRescaledSlope g c d m t) with hv_def
  set Image : Set Point3 := anisotropicRescalingMap g c d m '' E with hImage_def
  have h_exact_ad : PureWZ2PaperADSet1
      (scalarProjection v (horizontalSlice Image t))
      rho (1 - sigma) (Kakeya.realRpowENN rho (-loss)) :=
    pureWZ2_anisotropic_ad_transfer g c d m hcd hm hdelta hrho hrho_le_one hdelta_le_rho
      hsigma hsigma_lt_one hloss hC hC_top h_const h_old t ht
  have h_slice : horizontalSlice Y' t ⊆ horizontalSlice Image t := by
    exact Set.inter_subset_inter hY' (Set.Subset.refl _)
  have h_proj : scalarProjection v (horizontalSlice Y' t) ⊆
      scalarProjection v (horizontalSlice Image t) :=
    Set.image_mono h_slice
  exact h_exact_ad.weaken_subset h_proj

/-- Bridge from `PureWZ2PaperADSet1` (interval form) to `IsADSet1` (ball form).

A real ball `Metric.closedBall x r` equals the interval `Set.Icc (x-r) (x+r)`
of length `2*r`, so the covering ratio picks up a factor of `2`.  Since
`alpha ≤ 1`, we have `2^alpha ≤ 2`, so we absorb it into a factor of `2`.
-/
lemma PureWZ2PaperADSet1.toIsADSet1
    {E : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 E delta alpha C)
    (hE_bounded : E ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 E delta alpha (2 * C) := by
  rcases hAD with ⟨hdelta, halpha, halpha_one, hC_one, hC_top, hcover⟩
  have hC'_one : (1 : ENNReal) ≤ 2 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
    have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ (2 : ENNReal) * C := mul_le_mul' h2 h1
    simpa using h3
  have h_main : ∀ (rho : ℝ) (hrho : 0 ≤ rho), delta ≤ rho → rho ≤ 1 →
      ∀ (x r : ℝ), rho ≤ r → r ≤ 1 →
        (↑(Metric.externalCoveringNumber
          ⟨rho, hrho⟩
          (E ∩ Metric.closedBall x r)) : ENNReal) ≤
          (2 * C) * Kakeya.realRpowENN (r / rho) alpha := by
    intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
    have hrho_pos : 0 < rho := lt_of_lt_of_le hdelta hdelta_rho
    have hr_nonneg : 0 ≤ r := le_trans hrho hrho_r
    have h_ball : Metric.closedBall x r = Set.Icc (x - r) (x + r) := by
      ext y
      simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
      have h_iff : |y - x| ≤ r ↔ x - r ≤ y ∧ y ≤ x + r := by
        constructor
        · intro h
          have h' : -r ≤ y - x := (abs_le.mp h).1
          have h'' : y - x ≤ r := (abs_le.mp h).2
          constructor <;> linarith
        · rintro ⟨h1, h2⟩
          have h' : -r ≤ y - x := by linarith
          have h'' : y - x ≤ r := by linarith
          rw [abs_le] <;> exact ⟨h', h''⟩
      exact h_iff
    have h_set : E ∩ Metric.closedBall x r =
        E ∩ Set.Icc (x - r) (x + r) := by
      rw [h_ball]
    have h_rpos : 0 ≤ r / rho := div_nonneg hr_nonneg hrho
    have h4 := hcover rho hrho hdelta_rho (x - r) (2 * r) (by linarith)
    have h_endpoint : (x - r) + (2 * r) = x + r := by ring
    rw [h_endpoint] at h4
    rw [h_set]
    have h_rpow2_nonneg : 0 ≤ Real.rpow 2 alpha := Real.rpow_nonneg (by norm_num) alpha
    have h5 : Kakeya.realRpowENN ((2 * r) / rho) alpha =
        Kakeya.realRpowENN 2 alpha * Kakeya.realRpowENN (r / rho) alpha := by
      have h_eq1 : (2 * r) / rho = 2 * (r / rho) := by ring
      simp only [Kakeya.realRpowENN, h_eq1]
      have h_mul : Real.rpow (2 * (r / rho)) alpha =
          Real.rpow 2 alpha * Real.rpow (r / rho) alpha :=
        Real.mul_rpow (show (0 : ℝ) ≤ 2 from by norm_num) h_rpos
      rw [h_mul]
      have h_ofReal : ENNReal.ofReal (Real.rpow 2 alpha * Real.rpow (r / rho) alpha) =
          ENNReal.ofReal (Real.rpow 2 alpha) * ENNReal.ofReal (Real.rpow (r / rho) alpha) :=
        ENNReal.ofReal_mul h_rpow2_nonneg
      exact h_ofReal
    rw [h5] at h4
    have h7 : Kakeya.realRpowENN 2 alpha ≤ (2 : ENNReal) := by
      have h81 : Real.rpow 2 alpha ≤ Real.rpow 2 (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h82 : Real.rpow 2 (1 : ℝ) = 2 := by simp
      rw [h82] at h81
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h81
    have h_assoc : C * (Kakeya.realRpowENN 2 alpha * Kakeya.realRpowENN (r / rho) alpha) =
        (C * Kakeya.realRpowENN 2 alpha) * Kakeya.realRpowENN (r / rho) alpha := by
      rw [mul_assoc]
    rw [h_assoc] at h4
    set X : ENNReal := Kakeya.realRpowENN (r / rho) alpha with hX
    have h13 : C * Kakeya.realRpowENN 2 alpha ≤ C * (2 : ENNReal) :=
      mul_le_mul_of_nonneg_left h7 (show (0 : ENNReal) ≤ C from by simp)
    have h14 : (C * Kakeya.realRpowENN 2 alpha) * X ≤ (C * (2 : ENNReal)) * X :=
      mul_le_mul_of_nonneg_right h13 (show (0 : ENNReal) ≤ X from by simp)
    have h15 : (C * (2 : ENNReal)) * X = (2 * C) * X := by
      rw [mul_comm C (2 : ENNReal), mul_assoc]
    rw [h15] at h14
    exact h4.trans h14
  exact ⟨hdelta, halpha, halpha_one, hC'_one, hE_bounded, h_main⟩

end Kakeya.Assouad

end
