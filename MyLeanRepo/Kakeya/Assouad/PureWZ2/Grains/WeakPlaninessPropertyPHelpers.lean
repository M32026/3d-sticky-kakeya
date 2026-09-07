import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakPlaninessWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CloseDirectionCountBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgMassLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AbsorptionArithmetic
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import Mathlib.Tactic

/-!
# Helper lemmas for applying weak planiness to PropertyP subset

Provides:
1. `h_avg_m_val_ge_4R2`: m ≥ 4R+2 where R = (1600K+1)^5+1
2. `propertyOne_mass_lower`: propertyOne.mass ≥ (1/8) * L^(2*stickyLoss)
3. Transfer lemmas for hCV, hclose, hmult_upper from coarse to propertyOne
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Lower bound: `h_avg_m_val` is at least `4R+2` where `R = (1600K+1)^5+1`.

Since `m = 12 * max(A, B) + 12` and `B = (1600K+1)^5`, we have
`m ≥ 12B + 12 > 4(B+1) + 2 = 4R + 2`. -/
lemma h_avg_m_val_ge_4R2 (sigma stickyLoss L : ℝ) :
    4 * ((1600 * Nat.ceil (L ^ (-2 * ((sigma - 2 * stickyLoss) / 20))) + 1)^5 + 1) + 2 ≤
      PureWZ2.h_avg_m_val sigma stickyLoss L := by
  set K : ℕ := Nat.ceil (L ^ (-2 * ((sigma - 2 * stickyLoss) / 20))) with hK
  set B : ℕ := (1600 * K + 1)^5 with hB
  set A : ℕ := 2 * 4 * 601 ^ 3 * 12001 ^ 3 with hA
  have h1 : PureWZ2.h_avg_m_val sigma stickyLoss L = 12 * max A B + 12 := by
    rfl
  rw [h1]
  have h2 : 12 * max A B + 12 ≥ 12 * B + 12 := by
    have h3 : B ≤ max A B := le_max_right _ _
    nlinarith
  have h4 : 12 * B + 12 ≥ 4 * (B + 1) + 2 := by
    nlinarith
  linarith

/-- Mass decomposition: coarseShading.mass ≤ propertyOne.mass + m * volume(coarseShading.union).

The points not in propertyOne have multiplicity < m, so their contribution to mass
is at most m times their volume. -/
lemma propertyP_mass_decomposition
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (m : ℕ)
    (S : Set Point3)
    (hS_meas : MeasurableSet S)
    (hS_def : S = paperHighMultiplicitySet coarseShading (m : ENNReal))
    (propertyOne : WZ1PaperTubeShading coarse)
    (hPO_def : propertyOne = paperRestrictShadingToSet coarseShading S hS_meas) :
    coarseShading.mass ≤ propertyOne.mass + (m : ENNReal) * volume coarseShading.union := by
  let f : Point3 → ENNReal := fun p => (coarseShading.pointMultiplicity p : ENNReal)
  let T : Set Point3 := coarseShading.union \ S
  have h3 : S ⊆ coarseShading.union := by
    rw [hS_def]; intro p hp; exact hp.1
  have h_union_meas : MeasurableSet coarseShading.union := measurableSet_shading_union _
  have hT_meas : MeasurableSet T := h_union_meas.diff hS_meas
  have h_disj : Disjoint S T := disjoint_sdiff_right
  have h_union : S ∪ T = coarseShading.union := by
    rw [Set.union_sdiff_cancel h3]
  have h1 : propertyOne.mass = ∫⁻ p in S, f p := by
    rw [hPO_def]
    exact paperMassRestrictShadingToSet hS_meas
  have h_mass_union : coarseShading.mass = ∫⁻ p in coarseShading.union, f p := by
    have h_sum : ∑ i : Fin coarse.card, volume (coarseShading.carrier i ∩ coarseShading.union) =
        ∫⁻ p in coarseShading.union, f p :=
      sum_volume_inter_eq_setLIntegral_pointMultiplicity coarseShading h_union_meas
    have h2 : ∀ i, coarseShading.carrier i ∩ coarseShading.union = coarseShading.carrier i := by
      intro i; apply Set.inter_eq_left.mpr; intro x hx; exact ⟨i, hx⟩
    have h3 : ∑ i : Fin coarse.card, volume (coarseShading.carrier i ∩ coarseShading.union) = coarseShading.mass := by
      apply Finset.sum_congr rfl; intro i _; rw [h2 i]
    exact h3.symm.trans h_sum
  have h_split : ∫⁻ p in coarseShading.union, f p =
      (∫⁻ p in S, f p) + (∫⁻ p in T, f p) := by
    have h7 : ∫⁻ p in (S ∪ T), f p = (∫⁻ p in S, f p) + (∫⁻ p in T, f p) :=
      lintegral_union hT_meas h_disj
    rw [h_union] at h7
    exact h7
  have h_bound_T : ∫⁻ p in T, f p ≤ (m : ENNReal) * volume T := by
    have h_mult_lt : ∀ p ∈ T, f p < (m : ENNReal) := by
      intro p hp
      have h_not_S : p ∉ S := hp.2
      have h_in_union : p ∈ coarseShading.union := hp.1
      have h_iff : p ∈ S ↔ (m : ENNReal) ≤ f p := by
        rw [hS_def]
        simp [paperHighMultiplicitySet, f, h_in_union]
      have h : ¬((m : ENNReal) ≤ f p) := h_iff.not.mp h_not_S
      exact lt_of_not_ge h
    calc
      ∫⁻ p in T, f p ≤ ∫⁻ p in T, (m : ENNReal) := by
        apply MeasureTheory.setLIntegral_mono' hT_meas
        intro p hp; exact (h_mult_lt p hp).le
      _ = (m : ENNReal) * volume T := by
        rw [MeasureTheory.setLIntegral_const]
  have h_vol_T : volume T ≤ volume coarseShading.union := by
    apply MeasureTheory.measure_mono
    intro x hx
    exact hx.1
  calc
    coarseShading.mass
      = ∫⁻ p in coarseShading.union, f p := h_mass_union
    _ = (∫⁻ p in S, f p) + (∫⁻ p in T, f p) := h_split
    _ = propertyOne.mass + (∫⁻ p in T, f p) := by rw [←h1]
    _ ≤ propertyOne.mass + (m : ENNReal) * volume T := by gcongr
    _ ≤ propertyOne.mass + (m : ENNReal) * volume coarseShading.union := by gcongr

/-- Quantitative mass lower bound for propertyOne.

Given:
- coarseShading.mass ≥ (1/4) * L^(2*stickyLoss)
- m * volume(coarseShading.union) ≤ (1/8) * L^(2*stickyLoss)

Then propertyOne.mass ≥ (1/8) * L^(2*stickyLoss). -/
lemma propertyOne_mass_lower
    {L stickyLoss : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    {m : ℕ}
    {S : Set Point3}
    {hS_meas : MeasurableSet S}
    {hS_def : S = paperHighMultiplicitySet coarseShading (m : ENNReal)}
    {propertyOne : WZ1PaperTubeShading coarse}
    {hPO_def : propertyOne = paperRestrictShadingToSet coarseShading S hS_meas}
    (hL_pos : 0 < L)
    (_hstickyLoss_pos : 0 < stickyLoss)
    (h_mass_lower : (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) ≤ coarseShading.mass)
    (h_m_vol : (m : ENNReal) * volume coarseShading.union ≤ (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss)) :
    (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) ≤ propertyOne.mass := by
  set Xreal : ℝ := L ^ (2 * stickyLoss) with hXreal
  have hXreal_pos : 0 < Xreal := by positivity
  set X : ENNReal := ENNReal.ofReal Xreal with hX
  have hX_eq : X = Kakeya.realRpowENN L (2 * stickyLoss) := by
    simp [hX, hXreal, Kakeya.realRpowENN]
    <;> rfl
  have hX_ne_top : X ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_decomp : coarseShading.mass ≤ propertyOne.mass + (m : ENNReal) * volume coarseShading.union :=
    propertyP_mass_decomposition m S hS_meas hS_def propertyOne hPO_def
  have h_mass_lower' : (1 / 4 : ENNReal) * X ≤ coarseShading.mass := by
    rw [hX_eq]
    exact h_mass_lower
  have h_m_vol' : (m : ENNReal) * volume coarseShading.union ≤ (1 / 8 : ENNReal) * X := by
    rw [hX_eq]
    exact h_m_vol
  have h1 : (1 / 4 : ENNReal) * X ≤ propertyOne.mass + (m : ENNReal) * volume coarseShading.union :=
    le_trans h_mass_lower' h_decomp
  have h2 : (1 / 4 : ENNReal) * X ≤ propertyOne.mass + (1 / 8 : ENNReal) * X := by
    calc
      (1 / 4 : ENNReal) * X
        ≤ propertyOne.mass + (m : ENNReal) * volume coarseShading.union := h1
      _ ≤ propertyOne.mass + (1 / 8 : ENNReal) * X := by gcongr
  have h4_ne_zero : (4 : ENNReal) ≠ 0 := by simp
  have h4_ne_top : (4 : ENNReal) ≠ ⊤ := by simp
  have h8_ne_zero : (8 : ENNReal) ≠ 0 := by simp
  have h8_ne_top : (8 : ENNReal) ≠ ⊤ := by simp
  have h4inv : (4 : ENNReal) * (4 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h4_ne_zero h4_ne_top
  have h8inv : (8 : ENNReal) * (8 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h8_ne_zero h8_ne_top
  have h14 : (1 / 4 : ENNReal) = (4 : ENNReal)⁻¹ := by
    simp [div_eq_mul_inv]
  have h18 : (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ := by
    simp [div_eq_mul_inv]
  have h8a : (8 : ENNReal) * ((1 / 4 : ENNReal) * X) = 2 * X := by
    rw [h14]
    have h2 : (8 : ENNReal) = (2 : ENNReal) * (4 : ENNReal) := by norm_cast
    rw [h2]
    have h3 : (4 : ENNReal) * ((4 : ENNReal)⁻¹ * X) = X := by
      rw [← mul_assoc, h4inv, one_mul]
    have h4 : (2 : ENNReal) * (4 : ENNReal) * ((4 : ENNReal)⁻¹ * X) =
        (2 : ENNReal) * ((4 : ENNReal) * ((4 : ENNReal)⁻¹ * X)) := by
      rw [mul_assoc]
    rw [h4, h3]
  have h8b : (8 : ENNReal) * ((1 / 8 : ENNReal) * X) = X := by
    rw [h18]
    have h : (8 : ENNReal) * ((8 : ENNReal)⁻¹ * X) = ((8 : ENNReal) * (8 : ENNReal)⁻¹) * X := by
      rw [← mul_assoc]
    rw [h, h8inv, one_mul]
  have h3 : (8 : ENNReal) * ((1 / 4 : ENNReal) * X) ≤
      (8 : ENNReal) * (propertyOne.mass + (1 / 8 : ENNReal) * X) := by
    gcongr
  have h4 : (8 : ENNReal) * (propertyOne.mass + (1 / 8 : ENNReal) * X) =
      (8 : ENNReal) * propertyOne.mass + X := by
    rw [mul_add, h8b]
    <;> ring
  rw [h8a, h4] at h3
  have h5 : (2 : ENNReal) * X ≤ (8 : ENNReal) * propertyOne.mass + X := h3
  have h6 : X ≤ (8 : ENNReal) * propertyOne.mass := by
    have h7 : (2 : ENNReal) * X = X + X := by
      rw [two_mul]
      <;> ring
    rw [h7] at h5
    exact ENNReal.add_le_add_iff_right hX_ne_top |>.mp h5
  have h_final : (1 / 8 : ENNReal) * X ≤ propertyOne.mass := by
    calc
      (1 / 8 : ENNReal) * X
        ≤ (1 / 8 : ENNReal) * ((8 : ENNReal) * propertyOne.mass) := by gcongr
      _ = propertyOne.mass := by
        rw [h18]
        have h8inv' : (8 : ENNReal)⁻¹ * (8 : ENNReal) = 1 := by
          rw [mul_comm, h8inv]
        have h : (8 : ENNReal)⁻¹ * ((8 : ENNReal) * propertyOne.mass) = propertyOne.mass := by
          rw [← mul_assoc, h8inv', one_mul]
        exact h
  rw [hX_eq] at h_final
  exact h_final

/-- The high-multiplicity Property-P restriction keeps at least half of the
coarse shaded mass when the discarded multiplicity contribution is at most
one half.  This relative form is the input needed for fine parent-cell
pullback; unlike `propertyOne_mass_lower`, it does not discard the source mass
normalization. -/
lemma propertyOne_half_mass
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading propertyOne : WZ1PaperTubeShading coarse}
    {m : ℕ}
    {S : Set Point3}
    (hS_meas : MeasurableSet S)
    (hS_def : S = paperHighMultiplicitySet coarseShading (m : ENNReal))
    (hPO_def : propertyOne = paperRestrictShadingToSet coarseShading S hS_meas)
    (hcoarse_mass_ne_top : coarseShading.mass ≠ ⊤)
    (hdiscard :
      (m : ENNReal) * volume coarseShading.union ≤
        (1 / 2 : ENNReal) * coarseShading.mass) :
    (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyOne.mass := by
  have hdecomp :
      coarseShading.mass ≤
        propertyOne.mass + (m : ENNReal) * volume coarseShading.union :=
    propertyP_mass_decomposition m S hS_meas hS_def propertyOne hPO_def
  have hsum :
      coarseShading.mass ≤
        propertyOne.mass + (1 / 2 : ENNReal) * coarseShading.mass :=
    hdecomp.trans (by gcongr)
  have hhalf_finite :
      (1 / 2 : ENNReal) * coarseShading.mass ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hcoarse_mass_ne_top
  have hhalf_add : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
    have htwo :
        (1 / 2 : ENNReal) + (1 / 2 : ENNReal) =
          (2 : ENNReal) * (1 / 2 : ENNReal) := by
      rw [two_mul]
    rw [htwo]
    have hdiv : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
      simp [one_div]
    rw [hdiv]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hsplit :
      coarseShading.mass =
        (1 / 2 : ENNReal) * coarseShading.mass +
          (1 / 2 : ENNReal) * coarseShading.mass := by
    calc
      coarseShading.mass = 1 * coarseShading.mass := by simp
      _ = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) *
            coarseShading.mass := by rw [hhalf_add]
      _ = (1 / 2 : ENNReal) * coarseShading.mass +
            (1 / 2 : ENNReal) * coarseShading.mass := by rw [add_mul]
  have hsum' :
      (1 / 2 : ENNReal) * coarseShading.mass +
          (1 / 2 : ENNReal) * coarseShading.mass ≤
        propertyOne.mass + (1 / 2 : ENNReal) * coarseShading.mass := by
    rw [← hsplit]
    exact hsum
  exact (ENNReal.add_le_add_iff_right hhalf_finite).mp hsum'

/-- Transfer CV estimate from coarse shading to a subshading. -/
lemma transfer_cv_to_subshading
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading propertyOne : WZ1PaperTubeShading coarse}
    (hsub : PaperIsSubshading propertyOne coarseShading)
    (C : ENNReal)
    (hCV_coarse : ∀ (E : Set Point3), MeasurableSet E → E ⊆ coarseShading.union →
      ∀ (L_val : ENNReal),
        (∀ p ∈ E, L_val ≤ paperShadingTrilinearMultiplicity coarseShading p ^ (1 / 2 : ℝ)) →
          L_val * volume E ≤ C * (ENNReal.ofReal (L ^ 2) * coarse.enncard) ^ (3 / 2 : ℝ)) :
    ∀ (E : Set Point3), MeasurableSet E → E ⊆ propertyOne.union →
      ∀ (L_val : ENNReal),
        (∀ p ∈ E, L_val ≤ paperShadingTrilinearMultiplicity propertyOne p ^ (1 / 2 : ℝ)) →
          L_val * volume E ≤ C * (ENNReal.ofReal (L ^ 2) * coarse.enncard) ^ (3 / 2 : ℝ) := by
  intro E hE hE_sub L_val hLower
  have hunion_sub : propertyOne.union ⊆ coarseShading.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  have h1 : E ⊆ coarseShading.union := le_trans hE_sub hunion_sub
  have h2 : ∀ p ∈ E, paperShadingTrilinearMultiplicity propertyOne p ≤
      paperShadingTrilinearMultiplicity coarseShading p := by
    intro p _
    have h_indicator : ∀ (i : Fin coarse.card),
        Kakeya.CV.setIndicator (propertyOne.carrier i) p ≤
        Kakeya.CV.setIndicator (coarseShading.carrier i) p := by
      intro i
      have hsub_i : propertyOne.carrier i ⊆ coarseShading.carrier i := hsub i
      by_cases h : p ∈ propertyOne.carrier i
      · have h' : p ∈ coarseShading.carrier i := hsub_i h
        simp [Kakeya.CV.setIndicator, h, h']
      · simp [Kakeya.CV.setIndicator, h]
    have h_term : ∀ (i j k : Fin coarse.card),
        Kakeya.CV.setIndicator (propertyOne.carrier i) p *
        Kakeya.CV.setIndicator (propertyOne.carrier j) p *
        Kakeya.CV.setIndicator (propertyOne.carrier k) p *
        ENNReal.ofReal (Kakeya.CV.tripleVolume
          ![ (coarse.tube i).direction, (coarse.tube j).direction, (coarse.tube k).direction]) ≤
        Kakeya.CV.setIndicator (coarseShading.carrier i) p *
        Kakeya.CV.setIndicator (coarseShading.carrier j) p *
        Kakeya.CV.setIndicator (coarseShading.carrier k) p *
        ENNReal.ofReal (Kakeya.CV.tripleVolume
          ![ (coarse.tube i).direction, (coarse.tube j).direction, (coarse.tube k).direction]) := by
      intro i j k
      have hi := h_indicator i
      have hj := h_indicator j
      have hk := h_indicator k
      have htv_nonneg : 0 ≤ Kakeya.CV.tripleVolume
          ![ (coarse.tube i).direction, (coarse.tube j).direction, (coarse.tube k).direction] :=
        abs_nonneg _
      gcongr
      <;> assumption
    simp only [paperShadingTrilinearMultiplicity]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    exact h_term i j k
  have h3 : ∀ p ∈ E, L_val ≤ paperShadingTrilinearMultiplicity coarseShading p ^ (1 / 2 : ℝ) := by
    intro p hp
    have h4 : L_val ≤ paperShadingTrilinearMultiplicity propertyOne p ^ (1 / 2 : ℝ) := hLower p hp
    have h5 : paperShadingTrilinearMultiplicity propertyOne p ^ (1 / 2 : ℝ) ≤
        paperShadingTrilinearMultiplicity coarseShading p ^ (1 / 2 : ℝ) := by
      gcongr
      <;> exact h2 p hp
    exact le_trans h4 h5
  exact hCV_coarse E hE h1 L_val h3

/-- Transfer multiplicity upper bound from coarse shading to subshading. -/
lemma transfer_mult_upper_to_subshading
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading propertyOne : WZ1PaperTubeShading coarse}
    (hsub : PaperIsSubshading propertyOne coarseShading)
    (M : ℝ)
    (hmult_upper_coarse : ∀ p ∈ coarseShading.union,
        (coarseShading.pointMultiplicity p : ENNReal) ≤ ENNReal.ofReal M) :
    ∀ p ∈ propertyOne.union,
        (propertyOne.pointMultiplicity p : ENNReal) ≤ ENNReal.ofReal M := by
  intro p hp
  have hunion_sub : propertyOne.union ⊆ coarseShading.union := by
    intro q hq
    rcases hq with ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  have h1 : p ∈ coarseShading.union := hunion_sub hp
  have h2 : propertyOne.pointMultiplicity p ≤ coarseShading.pointMultiplicity p := by
    exact paperSubshading_pointMultiplicity_le propertyOne coarseShading hsub p
  exact le_trans (mod_cast h2) (hmult_upper_coarse p h1)

/-- Transfer close direction count from coarse shading to subshading. -/
lemma transfer_close_count_to_subshading
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading propertyOne : WZ1PaperTubeShading coarse}
    (hsub : PaperIsSubshading propertyOne coarseShading)
    (R : ℕ)
    (kappa : ℝ)
    (hclose_coarse : ∀ p ∈ coarseShading.union, ∀ i,
        p ∈ coarseShading.carrier i →
          paperCloseDirectionCount coarseShading p i kappa < R) :
    ∀ p ∈ propertyOne.union, ∀ i,
        p ∈ propertyOne.carrier i →
          paperCloseDirectionCount propertyOne p i kappa < R := by
  intro p hp i hi
  have hunion_sub : propertyOne.union ⊆ coarseShading.union := by
    intro q hq
    rcases hq with ⟨j, hj⟩
    exact ⟨j, hsub j hj⟩
  have h1 : p ∈ coarseShading.union := hunion_sub hp
  have h2 : p ∈ coarseShading.carrier i := hsub i hi
  have h3 : paperCloseDirectionCount propertyOne p i kappa ≤
      paperCloseDirectionCount coarseShading p i kappa :=
    close_direction_count_transfer (fun j => hsub j) p i kappa
  have h4 : paperCloseDirectionCount coarseShading p i kappa < R := hclose_coarse p h1 i h2
  exact lt_of_le_of_lt h3 h4

end Kakeya.Assouad

end
