import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedToDiscreteThinTubesStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedToDiscreteHelpers
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Smoothed-to-discrete thin tubes

Converts a `HasMeasureThinTubes` witness at smoothing radius `delta / 10` into a
`HasDiscreteThinTubes` witness at scale `delta` with constants `20 * K` and `2 * c`.
-/

noncomputable section

open MeasureTheory Set Metric Finset

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz1_smoothed_to_discrete_thin_tubes :
    WZ1SmoothedToDiscreteThinTubesStatement := by
  intro delta beta K c G₁ G₂ hG₁ hG₂ hdelta hbeta1 hc h2c hmt
  rcases hmt with ⟨hbeta, hK, ⟨hc_nonneg, hc_lt_one⟩, E, hE_meas, hE_sub, hE_mass, h_thin⟩
  set ρ : ℝ := delta / 10 with hρ_def
  have hρ : 0 < ρ := by linarith
  set ν₁ : ProbabilityMeasure Point2 := smoothMeasure G₁ hG₁ ρ hρ with hν₁_def
  set ν₂ : ProbabilityMeasure Point2 := smoothMeasure G₂ hG₂ ρ hρ with hν₂_def
  let σ : Point2 → ProbabilityMeasure Point2 := fun a => translatedBallMeasure ρ hρ a
  let μ : Point2 → Measure Point2 := fun a => (σ a : Measure Point2)

  let p : Point2 → Point2 → ENNReal := fun a b => ((μ a).prod (μ b)) E
  let E_disc : Finset (Point2 × Point2) :=
    (G₁ ×ˢ G₂).filter (fun ab => (1 / 2 : ENNReal) ≤ p ab.1 ab.2)

  have hE_disc_sub : E_disc ⊆ G₁ ×ˢ G₂ := filter_subset _ _

  have hp_le_one : ∀ (ab : Point2 × Point2), ab ∈ (G₁ ×ˢ G₂) → p ab.1 ab.2 ≤ 1 := by
    intro ab _
    have h_univ : ((σ ab.1).prod (σ ab.2) : Measure (Point2 × Point2)) Set.univ = 1 := by simp
    have h_le : ((σ ab.1).prod (σ ab.2) : Measure (Point2 × Point2)) E ≤
        ((σ ab.1).prod (σ ab.2) : Measure (Point2 × Point2)) Set.univ :=
      measure_mono (subset_univ E)
    rw [h_univ] at h_le
    exact h_le

  have h_coe_prod : (↑((ν₁.prod ν₂) E) : ENNReal) =
      ((ν₁ : Measure Point2).prod (ν₂ : Measure Point2)) E := by
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) E]
    rw [ProbabilityMeasure.toMeasure_prod]
    <;> rfl
  have hE_mass_ennreal : (1 - ENNReal.ofReal c) ≤
      ((ν₁ : Measure Point2).prod (ν₂ : Measure Point2)) E := by
    rw [← h_coe_prod]
    exact hE_mass

  have h_expand : ((ν₁ : Measure Point2).prod (ν₂ : Measure Point2)) E =
      (G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹ *
        ∑ a ∈ G₁, ∑ b ∈ G₂, p a b :=
    smoothMeasure_prod_expansion hG₁ hG₂ (hE := hE_meas)

  have h_sum_conv : ∑ ab ∈ (G₁ ×ˢ G₂), p ab.1 ab.2 =
      ∑ a ∈ G₁, ∑ b ∈ G₂, p a b := by
    rw [Finset.sum_product]

  set c1 : ENNReal := (G₁.card : ENNReal) with hc1_def
  set c2 : ENNReal := (G₂.card : ENNReal) with hc2_def
  have hc1_ne_zero : c1 ≠ 0 := by
    rw [hc1_def]
    have h : (G₁.card : ENNReal) ≠ 0 := by exact_mod_cast hG₁.card_pos.ne'
    exact h
  have hc2_ne_zero : c2 ≠ 0 := by
    rw [hc2_def]
    have h : (G₂.card : ENNReal) ≠ 0 := by exact_mod_cast hG₂.card_pos.ne'
    exact h
  have hc1_ne_top : c1 ≠ ⊤ := by
    rw [hc1_def] <;> simp
  have hc2_ne_top : c2 ≠ ⊤ := by
    rw [hc2_def] <;> simp

  have hE_mass' : (1 - ENNReal.ofReal c) * ((G₁ ×ˢ G₂).card : ENNReal) ≤
      ∑ ab ∈ (G₁ ×ˢ G₂), p ab.1 ab.2 := by
    rw [h_expand] at hE_mass_ennreal
    have h_card : ((G₁ ×ˢ G₂).card : ENNReal) = c1 * c2 := by
      simp [Finset.card_product, hc1_def, hc2_def] <;> norm_cast
    rw [h_sum_conv, h_card]
    let S : ENNReal := ∑ a ∈ G₁, ∑ b ∈ G₂, p a b
    have h_alg : (c1⁻¹ * c2⁻¹ * S) * (c1 * c2) = S := by
      have h1 : c1⁻¹ * c1 = 1 := ENNReal.inv_mul_cancel hc1_ne_zero hc1_ne_top
      have h2 : c2⁻¹ * c2 = 1 := ENNReal.inv_mul_cancel hc2_ne_zero hc2_ne_top
      have h_comm : (c1⁻¹ * c2⁻¹ * S) * (c1 * c2) =
          (c1⁻¹ * c1) * (c2⁻¹ * c2) * S := by
        simp only [mul_assoc]
        <;> ac_rfl
      rw [h_comm, h1, h2] <;> simp
    calc
      (1 - ENNReal.ofReal c) * (c1 * c2)
        ≤ (c1⁻¹ * c2⁻¹ * S) * (c1 * c2) := by gcongr
      _ = S := h_alg

  have h_markov : (1 - ENNReal.ofReal (2 * c)) *
      ((G₁ ×ˢ G₂).card : ENNReal) ≤ (E_disc.card : ENNReal) :=
    have hS_nonempty : (G₁ ×ˢ G₂).Nonempty := Finset.Nonempty.product hG₁ hG₂
    markov_retention hS_nonempty (fun ab : Point2 × Point2 => p ab.1 ab.2)
      hp_le_one hc h2c hE_mass'

  have h_card_prod : ((G₁ ×ˢ G₂).card : ENNReal) = c1 * c2 := by
    simp [Finset.card_product, hc1_def, hc2_def] <;> norm_cast

  have h_mass_final : (1 - ENNReal.ofReal (2 * c)) * c1 * c2 ≤
      (E_disc.card : ENNReal) := by
    rw [h_card_prod] at h_markov
    simpa [mul_assoc] using h_markov

  have h_null : ∀ (b : Point2), (μ b) (Metric.ball b ρ)ᶜ = 0 := by
    intro b
    have h_def : μ b = ↑((ballUniformMeasure ρ hρ).map
        (f := fun y : Point2 => b + y)
        (f_aemble := (by fun_prop : Measurable (fun y : Point2 => b + y)).aemeasurable)) := by
      simp [μ, σ, translatedBallMeasure] <;> rfl
    have h_map : (μ b) (Metric.ball b ρ)ᶜ =
        (ballUniformMeasure ρ hρ : Measure Point2)
          {y : Point2 | b + y ∈ (Metric.ball b ρ)ᶜ} := by
      rw [h_def]
      rw [ProbabilityMeasure.map_apply' (ballUniformMeasure ρ hρ)
        (f_aemble := (by fun_prop : Measurable (fun y : Point2 => b + y)).aemeasurable)
        Metric.isOpen_ball.measurableSet.compl]
      <;> rfl
    rw [h_map]
    have h_eq : {y : Point2 | b + y ∈ (Metric.ball b ρ)ᶜ} =
        (Metric.ball (0 : Point2) ρ)ᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Metric.mem_ball]
      <;> simp [dist_eq_norm] <;> abel
    rw [h_eq]
    rw [ballUniformMeasure_apply hρ (Metric.isOpen_ball.measurableSet.compl)]
    have h3 : Metric.ball (0 : Point2) ρ ∩
        (Metric.ball (0 : Point2) ρ)ᶜ = (∅ : Set Point2) := by
      ext x
      simp
    rw [h3] <;> simp

  have h_supp_incl : ∀ (a : Point2), a ∈ G₁ →
      (μ a).support ⊆ (ν₁ : Measure Point2).support := by
    intro a ha
    have h6 : (ν₁ : Measure Point2) = c1⁻¹ • ∑ a' ∈ G₁, μ a' := by
      rw [hν₁_def] <;> rfl
    have h7 : μ a ≤ ∑ a' ∈ G₁, μ a' := by
      apply Finset.single_le_sum
      · intro i _
        exact bot_le
      · exact ha
    have h8 : c1⁻¹ • μ a ≤ (ν₁ : Measure Point2) := by
      rw [h6] <;> gcongr <;> exact h7
    intro x hx
    simp only [Measure.mem_support_iff_forall] at hx ⊢
    intro U hU
    have h_pos1 : 0 < (μ a) U := hx U hU
    have h_pos2 : 0 < c1⁻¹ := by
      have h : c1⁻¹ ≠ 0 := by
        intro h_contra
        have h' : c1 = ⊤ := ENNReal.inv_eq_zero.mp h_contra
        exact hc1_ne_top h'
      exact Ne.bot_lt h
    have h_pos : 0 < (c1⁻¹ • μ a) U := by
      rw [Measure.smul_apply]
      have h_ne1 : c1⁻¹ ≠ 0 := h_pos2.ne'
      have h_ne2 : (μ a) U ≠ 0 := h_pos1.ne'
      have h_mul_ne : (c1⁻¹ * (μ a) U) ≠ 0 := by
        simpa [mul_eq_zero] using not_or.mpr ⟨h_ne1, h_ne2⟩
      exact h_mul_ne.bot_lt
    have h_le : (c1⁻¹ • μ a) U ≤ (ν₁ : Measure Point2) U := h8 U
    exact h_pos.trans_le h_le

  have h_ae_supp : ∀ (a : Point2), a ∈ G₁ →
      ∀ᵐ x ∂(μ a), x ∈ (ν₁ : Measure Point2).support := by
    intro a ha
    have h4 : ∀ᵐ x ∂(μ a), x ∈ (μ a).support := (μ a).support_mem_ae
    exact h4.mono (fun x hx => h_supp_incl a ha hx)

  have h_ae_ball : ∀ (a : Point2), a ∈ G₁ →
      ∀ᵐ x ∂(μ a), x ∈ Metric.ball a ρ := by
    intro a _
    rw [ae_iff]
    have h_set : {x : Point2 | x ∉ Metric.ball a ρ} =
        (Metric.ball a ρ)ᶜ := by
      ext x
      simp
    rw [h_set]
    exact h_null a

  have h_tube_bound : ∀ (a : Point2), a ∈ G₁ →
      ∀ (ℓ : AffineSubspace ℝ Point2),
      a ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ (r : ℝ), delta ≤ r →
        ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
          (a, b₂) ∈ E_disc)).card : ENNReal) ≤
          ENNReal.ofReal (20 * K * r ^ beta) * c2 := by
    intro a ha ℓ ha_in_ℓ hfin r hr
    let S : Finset Point2 :=
      G₂.filter (fun b₂ =>
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
        (a, b₂) ∈ E_disc)
    by_cases hS : S.Nonempty
    · rcases hS with ⟨b, hb⟩
      have hbG : b ∈ G₂ := (mem_filter.mp hb).1
      have hb_thick : b ∈ Metric.thickening r (ℓ : Set Point2) :=
        (mem_filter.mp hb).2.1
      have h_ab_in_Edisc : (a, b) ∈ E_disc := (mem_filter.mp hb).2.2
      have hpb : (1 / 2 : ENNReal) ≤ p a b :=
        (Finset.mem_filter.mp h_ab_in_Edisc).2

      let F : Point2 → Set Point2 := fun x =>
        {y | y ∈ Metric.thickening (r + 2 * ρ)
            (AffineSubspace.mk' x ℓ.direction : Set Point2) ∧
          (x, y) ∈ E}

      have hF_meas : ∀ (x : Point2), MeasurableSet (F x) := by
        intro x
        have h1 : MeasurableSet
            (Metric.thickening (r + 2 * ρ)
              (AffineSubspace.mk' x ℓ.direction : Set Point2)) :=
          Metric.isOpen_thickening.measurableSet
        have h2 : MeasurableSet {y : Point2 | (x, y) ∈ E} :=
          hE_meas.preimage (by fun_prop : Measurable (fun y => (x, y)))
        exact h1.inter h2

      have h_contain : ∀ (x : Point2), x ∈ Metric.ball a ρ →
          ∀ (b' : Point2), b' ∈ S →
          (μ b') {y : Point2 | (x, y) ∈ E} ≤ (μ b') (F x) := by
        intro x hx b' hb'
        have hb'_thick : b' ∈ Metric.thickening r (ℓ : Set Point2) :=
          (mem_filter.mp hb').2.1
        have h1 : {y : Point2 | (x, y) ∈ E} ⊆
            F x ∪ (Metric.ball b' ρ)ᶜ := by
          intro y hy
          by_cases hys : y ∈ Metric.ball b' ρ
          · have h2 : y ∈ F x := by
              have h3 : y ∈ Metric.thickening (r + 2 * ρ)
                  (AffineSubspace.mk' x ℓ.direction : Set Point2) :=
                thickening_parallel_enlargement ha_in_ℓ hx hys hb'_thick
              exact ⟨h3, hy⟩
            exact Or.inl h2
          · exact Or.inr hys
        have h2 : (μ b') {y : Point2 | (x, y) ∈ E} ≤
            (μ b') (F x ∪ (Metric.ball b' ρ)ᶜ) :=
          measure_mono h1
        have h3 : (μ b') (F x ∪ (Metric.ball b' ρ)ᶜ) ≤
            (μ b') (F x) + (μ b') (Metric.ball b' ρ)ᶜ :=
          measure_union_le _ _
        rw [h_null b'] at h3
        simpa using h2.trans h3

      have h_sum_bound : ∀ (x : Point2), x ∈ Metric.ball a ρ →
          x ∈ (ν₁ : Measure Point2).support →
          ∑ b' ∈ S, (μ b') {y : Point2 | (x, y) ∈ E} ≤
            c2 * ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
        intro x hx_ball hx_supp
        have h1 : ∑ b' ∈ S, (μ b') {y : Point2 | (x, y) ∈ E} ≤
            ∑ b' ∈ S, (μ b') (F x) := by
          apply Finset.sum_le_sum
          intro b' hb'
          exact h_contain x hx_ball b' hb'
        have h2 : ∑ b' ∈ S, (μ b') (F x) ≤
            ∑ b' ∈ G₂, (μ b') (F x) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact filter_subset _ _
          · intro i _ _
            positivity
        let msum : Measure Point2 := ∑ b' ∈ G₂, μ b'
        have h4 : (ν₂ : Measure Point2) = c2⁻¹ • msum := by
          rw [hν₂_def] <;> rfl
        have h5 : (ν₂ : Measure Point2) (F x) = c2⁻¹ * msum (F x) := by
          rw [h4]
          exact MeasureTheory.Measure.smul_apply
            (R := ENNReal) (c := c2⁻¹) (μ := msum) (s := F x)
        have h6 : msum (F x) = ∑ b' ∈ G₂, (μ b') (F x) := by
          rw [Measure.finsetSum_apply]
        have h3 : ∑ b' ∈ G₂, (μ b') (F x) =
            c2 * (ν₂ : Measure Point2) (F x) := by
          rw [h6] at h5
          calc
            ∑ b' ∈ G₂, (μ b') (F x)
                = c2 * (c2⁻¹ * ∑ b' ∈ G₂, (μ b') (F x)) := by
                    have h_cancel :
                        c2 * (c2⁻¹ * ∑ b' ∈ G₂, (μ b') (F x)) =
                          ∑ b' ∈ G₂, (μ b') (F x) := by
                      rw [←mul_assoc,
                        ENNReal.mul_inv_cancel hc2_ne_zero hc2_ne_top,
                        one_mul]
                    exact h_cancel.symm
            _ = c2 * (ν₂ : Measure Point2) (F x) := by rw [h5]
        have hrpos : 0 < r + 2 * ρ := by linarith
        let ℓ_x : AffineSubspace ℝ Point2 :=
          AffineSubspace.mk' x ℓ.direction
        have hx_in_ℓx : x ∈ (ℓ_x : Set Point2) := by simp [ℓ_x]
        have h_dir : ℓ_x.direction = ℓ.direction := by
          simp [ℓ_x, AffineSubspace.direction_mk']
        have hfin_x : Module.finrank ℝ ℓ_x.direction = 1 := by
          rw [h_dir]
          exact hfin
        have h_thin' :
            ν₂ (F x) ≤ Real.toNNReal (K * (r + 2 * ρ) ^ beta) :=
          h_thin x hx_supp ℓ_x hx_in_ℓx hfin_x
            (r + 2 * ρ) hrpos
        have h_nonneg : 0 ≤ K * (r + 2 * ρ) ^ beta := by positivity
        have h7 : (ν₂ : Measure Point2) (F x) ≤
            ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
          have h_coe : (↑(ν₂ (F x)) : ENNReal) =
              (ν₂ : Measure Point2) (F x) :=
            ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ (F x)
          rw [← h_coe]
          have h8 : (↑(ν₂ (F x)) : ENNReal) ≤
              ↑(Real.toNNReal (K * (r + 2 * ρ) ^ beta)) := by
            exact_mod_cast h_thin'
          have h9 :
              (↑(Real.toNNReal (K * (r + 2 * ρ) ^ beta)) : ENNReal) =
                ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) :=
            ENNReal.ofNNReal_toNNReal (K * (r + 2 * ρ) ^ beta)
          rw [h9] at h8
          exact h8
        calc
          ∑ b' ∈ S, (μ b') {y : Point2 | (x, y) ∈ E}
              ≤ ∑ b' ∈ S, (μ b') (F x) := h1
          _ ≤ ∑ b' ∈ G₂, (μ b') (F x) := h2
          _ = c2 * (ν₂ : Measure Point2) (F x) := h3
          _ ≤ c2 * ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
            gcongr

      have h_ae : ∀ᵐ x ∂(μ a),
          ∑ b' ∈ S, (μ b') {y : Point2 | (x, y) ∈ E} ≤
            c2 * ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
        filter_upwards [h_ae_ball a ha, h_ae_supp a ha]
          with x hx_ball hx_supp
        exact h_sum_bound x hx_ball hx_supp

      have h_fubini : ∀ (b' : Point2), p a b' =
          ∫⁻ x, (μ b') {y : Point2 | (x, y) ∈ E} ∂(μ a) := by
        intro b'
        have h : ((μ a).prod (μ b')) E =
            ∫⁻ x, (μ b') (Prod.mk x ⁻¹' E) ∂(μ a) :=
          Measure.prod_apply hE_meas
        have h_pre : ∀ (x : Point2),
            (Prod.mk x ⁻¹' E) = {y : Point2 | (x, y) ∈ E} := by
          intro x
          rfl
        simpa [p, h_pre] using h

      have h_sum_p : ∑ b' ∈ S, p a b' =
          ∫⁻ x, ∑ b' ∈ S, (μ b') {y : Point2 | (x, y) ∈ E} ∂(μ a) := by
        have h_eq1 : ∑ b' ∈ S, p a b' =
            ∑ b' ∈ S,
              ∫⁻ x, (μ b') {y | (x, y) ∈ E} ∂(μ a) := by
          apply Finset.sum_congr rfl
          intro b' _
          exact h_fubini b'
        rw [h_eq1]
        have h_lint :
            (∑ b' ∈ S,
              ∫⁻ x, (μ b') {y | (x, y) ∈ E} ∂(μ a)) =
              ∫⁻ x, ∑ b' ∈ S,
                (μ b') {y | (x, y) ∈ E} ∂(μ a) := by
          have h_meas : ∀ (b' : Point2), b' ∈ S →
              Measurable
                (fun x : Point2 => (μ b') {y : Point2 | (x, y) ∈ E}) := by
            intro b' _
            let E_swap : Set (Point2 × Point2) := Prod.swap ⁻¹' E
            have hE_swap : MeasurableSet E_swap :=
              hE_meas.preimage measurable_swap
            have h1 :
                (fun x : Point2 =>
                  (μ b') {y : Point2 | (x, y) ∈ E}) =
                  fun x : Point2 =>
                    (μ b') ((fun y : Point2 => (y, x)) ⁻¹' E_swap) := by
              funext x
              rfl
            rw [h1]
            exact measurable_measure_prodMk_right hE_swap
          exact (MeasureTheory.lintegral_finsetSum S (hf := h_meas)).symm
        exact h_lint

      have h9 : ∑ b' ∈ S, p a b' ≤
          c2 * ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
        rw [h_sum_p]
        have h10 :
            ∫⁻ x, ∑ b' ∈ S,
                (μ b') {y : Point2 | (x, y) ∈ E} ∂(μ a) ≤
              ∫⁻ x, c2 *
                ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) ∂(μ a) :=
          lintegral_mono_ae h_ae
        have h11 :
            ∫⁻ x, c2 *
                ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) ∂(μ a) =
              c2 * ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) := by
          rw [lintegral_const]
          have h_univ : (μ a) Set.univ = 1 := by simp
          rw [h_univ, mul_one]
        rw [h11] at h10
        exact h10

      have h10 : ∀ b' ∈ S, (1 / 2 : ENNReal) ≤ p a b' := by
        intro b' hb'
        have h_ab_in : (a, b') ∈ E_disc := (mem_filter.mp hb').2.2
        simpa using (Finset.mem_filter.mp h_ab_in).2

      have h11 : (S.card : ENNReal) * (1 / 2 : ENNReal) ≤
          ∑ b' ∈ S, p a b' := by
        have h : ∑ b' ∈ S, (1 / 2 : ENNReal) =
            (S.card : ENNReal) * (1 / 2 : ENNReal) := by
          have h' : ∑ b' ∈ S, (1 / 2 : ENNReal) =
              (S.card : ℕ) • (1 / 2 : ENNReal) := by
            rw [Finset.sum_const]
          rw [h']
          simp [nsmul_eq_mul]
        rw [←h]
        apply Finset.sum_le_sum
        intro b' hb'
        exact h10 b' hb'

      have h12 : (S.card : ENNReal) ≤
          c2 * ENNReal.ofReal (2 * K * (r + 2 * ρ) ^ beta) := by
        set X : ENNReal :=
          ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) with hX_def
        have h13 : (S.card : ENNReal) * (1 / 2 : ENNReal) ≤
            c2 * X := h11.trans h9
        have h_half : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          have h_div : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
            simp [div_eq_mul_inv]
          rw [h_div]
          rw [ENNReal.mul_inv_cancel] <;> norm_num
        have h14 : (S.card : ENNReal) =
            (2 : ENNReal) *
              ((S.card : ENNReal) * (1 / 2 : ENNReal)) := by
          have h_comm :
              (2 : ENNReal) *
                  ((S.card : ENNReal) * (1 / 2 : ENNReal)) =
                (S.card : ENNReal) *
                  ((2 : ENNReal) * (1 / 2 : ENNReal)) := by
            rw [mul_left_comm]
          rw [h_comm, h_half, mul_one]
        have hK2 : 0 ≤ K := by linarith
        have h_exp2 : 0 ≤ (r + 2 * ρ) ^ beta := by
          have h_pos : 0 ≤ r + 2 * ρ := by linarith
          exact Real.rpow_nonneg h_pos beta
        have h_nonneg : 0 ≤ K * (r + 2 * ρ) ^ beta :=
          mul_nonneg hK2 h_exp2
        have h9 : (2 : ENNReal) * X =
            ENNReal.ofReal (2 * K * (r + 2 * ρ) ^ beta) := by
          rw [hX_def]
          have h10 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
          rw [h10]
          have h11 :
              ENNReal.ofReal 2 *
                  ENNReal.ofReal (K * (r + 2 * ρ) ^ beta) =
                ENNReal.ofReal
                  (2 * (K * (r + 2 * ρ) ^ beta)) := by
            rw [← ENNReal.ofReal_mul (hp := by norm_num)]
          rw [h11]
          have h12 :
              2 * (K * (r + 2 * ρ) ^ beta) =
                2 * K * (r + 2 * ρ) ^ beta := by ring
          rw [h12]
        have h_conv : (2 : ENNReal) * (c2 * X) =
            c2 * ((2 : ENNReal) * X) := by
          have h : (2 : ENNReal) * (c2 * X) =
              ((2 : ENNReal) * c2) * X := by rw [mul_assoc]
          rw [h]
          have h2 : (2 : ENNReal) * c2 =
              c2 * (2 : ENNReal) := by
            apply mul_comm
          rw [h2, mul_assoc]
        calc
          (S.card : ENNReal)
              = (2 : ENNReal) *
                  ((S.card : ENNReal) * (1 / 2 : ENNReal)) := h14
          _ ≤ (2 : ENNReal) * (c2 * X) := by gcongr
          _ = c2 * ((2 : ENNReal) * X) := h_conv
          _ = c2 * ENNReal.ofReal
              (2 * K * (r + 2 * ρ) ^ beta) := by rw [h9]

      have h15 : r + 2 * ρ ≤ (6 / 5 : ℝ) * r := by
        have h16 : 2 * ρ = delta / 5 := by
          rw [hρ_def] <;> ring
        rw [h16]
        linarith
      have h17 : 0 ≤ r + 2 * ρ := by linarith
      have h18 : (r + 2 * ρ) ^ beta ≤
          ((6 / 5 : ℝ) * r) ^ beta :=
        Real.rpow_le_rpow h17 h15 hbeta
      have h19 : ((6 / 5 : ℝ) * r) ^ beta =
          (6 / 5 : ℝ) ^ beta * r ^ beta := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
      have h20 : (6 / 5 : ℝ) ^ beta ≤ (6 / 5 : ℝ) := by
        have h21 : (1 : ℝ) ≤ (6 / 5 : ℝ) := by norm_num
        have h22 : (6 / 5 : ℝ) ^ beta ≤
            (6 / 5 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h21 hbeta1
        have h23 : (6 / 5 : ℝ) ^ (1 : ℝ) = (6 / 5 : ℝ) := by simp
        rw [h23] at h22
        exact h22
      have h24 : 2 * K * (r + 2 * ρ) ^ beta ≤
          20 * K * r ^ beta := by
        have h25 : 0 ≤ K := by linarith
        have h_rpos : 0 ≤ r := by linarith
        have h26 : 0 ≤ r ^ beta := Real.rpow_nonneg h_rpos beta
        calc
          2 * K * (r + 2 * ρ) ^ beta
              ≤ 2 * K * (((6 / 5 : ℝ) * r) ^ beta) := by
                gcongr
          _ = 2 * K * ((6 / 5 : ℝ) ^ beta * r ^ beta) := by
            rw [h19]
          _ ≤ 2 * K * ((6 / 5 : ℝ) * r ^ beta) := by
            gcongr
          _ = (12 / 5 : ℝ) * K * r ^ beta := by ring
          _ ≤ 20 * K * r ^ beta := by
            have h27 : 0 ≤ K * r ^ beta := by positivity
            nlinarith
      have h28 :
          ENNReal.ofReal (2 * K * (r + 2 * ρ) ^ beta) ≤
            ENNReal.ofReal (20 * K * r ^ beta) :=
        ENNReal.ofReal_le_ofReal h24
      have h_final : (S.card : ENNReal) ≤
          ENNReal.ofReal (20 * K * r ^ beta) * c2 := by
        calc
          (S.card : ENNReal)
              ≤ c2 * ENNReal.ofReal
                  (2 * K * (r + 2 * ρ) ^ beta) := h12
          _ ≤ c2 * ENNReal.ofReal (20 * K * r ^ beta) := by
            gcongr
          _ = ENNReal.ofReal (20 * K * r ^ beta) * c2 := by
            rw [mul_comm]
      exact h_final

    · have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have h_goal : (S.card : ENNReal) ≤
          ENNReal.ofReal (20 * K * r ^ beta) * c2 := by
        rw [h_empty] <;> simp
      simpa [S] using h_goal

  have h2c' : (2 * c) ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hK20 : 1 ≤ 20 * K := by
    have h1 : 1 ≤ K := hK
    have h2 : K ≤ 20 * K := by
      have h3 : 0 ≤ K := by linarith
      nlinarith
    linarith

  exact
    ⟨hbeta, hK20, h2c', E_disc, hE_disc_sub, h_mass_final, h_tube_bound⟩

end Kakeya.Assouad
