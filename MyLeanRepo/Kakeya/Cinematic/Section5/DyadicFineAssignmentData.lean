import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.TwoEndsBridge

/-!
# Dyadic fine assignment with pointwise two-ends certificates

Dyadic pigeonholing fixes common upper representatives for the metric and
tangency scales, but the selected metric ball, center, and retained fibers
remain point-dependent. This structure carries those exact pointwise
certificates alongside the common-scale fine rectangle assignment.
-/

noncomputable section

namespace Kakeya.Cinematic

lemma FiniteFunctionFamily.HasKatzTaoBound.rescale_base
    {F : FiniteFunctionFamily}
    {baseDelta scale C_KT : ℝ}
    (hKT : F.HasKatzTaoBound baseDelta C_KT)
    (hbaseDelta : 0 < baseDelta)
    (hscale : 1 ≤ scale) :
    F.HasKatzTaoBound
      (scale * baseDelta) (scale * C_KT) := by
  constructor
  · calc
      (F.card : ℝ) ≤ C_KT / baseDelta := hKT.1
      _ = (scale * C_KT) / (scale * baseDelta) := by
        field_simp [hbaseDelta.ne', (zero_lt_one.trans_le hscale).ne']
  · intro center radius hradius hradOne
    have hbaseRadius : baseDelta ≤ radius := by
      calc
        baseDelta = 1 * baseDelta := by ring
        _ ≤ scale * baseDelta := by
          gcongr
        _ ≤ radius := hradius
    calc
      ((F.carrier ∩ c2Ball center radius).ncard : ℝ) ≤
          C_KT * (radius / baseDelta) :=
        hKT.2 center radius hbaseRadius hradOne
      _ =
          (scale * C_KT) /
            (scale * baseDelta) * radius := by
        field_simp [hbaseDelta.ne', (zero_lt_one.trans_le hscale).ne']
      _ =
          (scale * C_KT) *
            (radius / (scale * baseDelta)) := by ring

structure DyadicFineAssignmentData
    (family : Set C2Function) (E : Set (ℝ × ℝ))
    (K delta diameter epsilon eta tRep DeltaRep C_R : ℝ) where
  interval : ParameterInterval
  assignment :
    FineRectangleAssignmentData
      family E K delta tRep DeltaRep C_R
  assignment_interval : assignment.interval = interval
  exactT : E → ℝ
  exactDelta : E → ℝ
  ambientSource : FiniteFunctionFamily
  ambientSource_subset : ambientSource.carrier ⊆ family
  separationScale : ℝ
  separationScale_pos : 0 < separationScale
  ambientSource_separated :
    ambientSource.IsDeltaSeparated separationScale
  source : E → FiniteFunctionFamily
  source_subset_ambient : ∀ p : E,
    (source p).carrier ⊆ ambientSource.carrier
  metricFiber : E → FiniteFunctionFamily
  tangencyFiber : E → FiniteFunctionFamily
  metricCenter : E → C2Function
  tangencyCenter : E → C2Function
  tangencyCenter_ball_measurable : ∀ center radius,
    MeasurableSet
      {q : ℝ × ℝ | ∃ hq : q ∈ E,
        tangencyCenter ⟨q, hq⟩ ∈ c2Ball center radius}
  epsilon_pos : 0 < epsilon
  eta_pos : 0 < eta
  mu : ℕ
  mu_pos : 0 < mu
  mu_le_source : ∀ p : E, mu ≤ (source p).card
  certificate : ∀ p : E,
    TwoEndsCertificate interval delta diameter epsilon eta
      (exactT p) (exactDelta p)
      (source p) (metricFiber p) (tangencyFiber p)
      (metricCenter p) (tangencyCenter p)
  delta_le_DeltaRep : delta ≤ DeltaRep
  DeltaRep_le_tRep : DeltaRep ≤ tRep
  tRep_pos : 0 < tRep
  four_exactT_le_rep : ∀ p : E, 4 * exactT p ≤ tRep
  exactDelta_le_rep : ∀ p : E, exactDelta p ≤ DeltaRep
  rep_le_eight_exactT : ∀ p : E, tRep ≤ 8 * exactT p
  repDelta_le_two_exactDelta : ∀ p : E,
    DeltaRep ≤ 2 * exactDelta p
  assignment_center : ∀ p : E,
    assignment.center p = tangencyCenter p
  assignment_fiber : ∀ p : E,
    assignment.fiber p = tangencyFiber p

namespace DyadicFineAssignmentData

variable
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)

lemma fiber_subset_metric (p : E) :
    (data.assignment.fiber p).carrier ⊆
      (data.metricFiber p).carrier := by
  intro f hf
  rw [data.assignment_fiber p] at hf
  rw [(data.certificate p).tangencyFiber_eq] at hf
  exact hf.1

lemma fiber_subset_source (p : E) :
    (data.assignment.fiber p).carrier ⊆
      (data.source p).carrier := by
  exact (data.fiber_subset_metric p).trans
    ((data.certificate p).metric_subset.trans
      Set.inter_subset_left)

lemma fiber_subset_ambient (p : E) :
    (data.assignment.fiber p).carrier ⊆
      data.ambientSource.carrier := by
  exact (data.fiber_subset_source p).trans
    (data.source_subset_ambient p)

lemma fiber_card_le_source (p : E) :
    (data.assignment.fiber p).card ≤
      (data.source p).card := by
  exact Set.ncard_le_ncard
    (data.fiber_subset_source p) (data.source p).finite

lemma fiber_card_cast_le_source (p : E) :
    ((data.assignment.fiber p).card : ℝ) ≤
      ((data.source p).card : ℝ) := by
  exact_mod_cast data.fiber_card_le_source p

lemma fiber_separated (p : E) :
    (data.assignment.fiber p).IsDeltaSeparated
      data.separationScale := by
  intro f hf g hg hfg
  exact data.ambientSource_separated
    (data.fiber_subset_ambient p hf)
    (data.fiber_subset_ambient p hg) hfg

lemma center_mem_metric (p : E) :
    data.assignment.center p ∈
      (data.metricFiber p).carrier := by
  rw [data.assignment_center p]
  exact (data.certificate p).tangencyCenter_mem

lemma center_mem_fiber
    (hdelta : 0 < delta) (p : E) :
    data.assignment.center p ∈
      (data.assignment.fiber p).carrier := by
  rw [data.assignment_center p, data.assignment_fiber p]
  rw [(data.certificate p).tangencyFiber_eq]
  refine ⟨(data.certificate p).tangencyCenter_mem, ?_⟩
  have hnonneg :=
    localAssembly_tangencyParameterOn_nonneg
      data.interval (data.tangencyCenter p)
        (data.tangencyCenter p)
  have hupper :=
    localAssembly_tangencyParameterOn_le
      data.interval (data.tangencyCenter p)
        (data.tangencyCenter p)
  have hzero :
      tangencyParameterOn data.interval
        (data.tangencyCenter p) (data.tangencyCenter p) = 0 := by
    rw [c2Distance_eq_dist, dist_self] at hupper
    linarith
  change tangencyParameterOn data.interval
      (data.tangencyCenter p) (data.tangencyCenter p) ≤
    data.exactDelta p
  rw [hzero]
  exact hdelta.le.trans (data.certificate p).delta_le_Delta

lemma fiber_nonempty
    (hdelta : 0 < delta) (p : E) :
    (data.assignment.fiber p).carrier.Nonempty :=
  ⟨data.assignment.center p, data.center_mem_fiber hdelta p⟩

lemma fiber_card_pos
    (hdelta : 0 < delta) (p : E) :
    0 < (data.assignment.fiber p).card := by
  exact (Set.ncard_pos (data.assignment.fiber p).finite).2
    (data.fiber_nonempty hdelta p)

lemma fiber_dist_le_representative
    (hdelta : 0 < delta)
    (p : E) (f : C2Function)
    (hf : f ∈ (data.assignment.fiber p).carrier) :
    c2Distance f (data.assignment.center p) ≤ tRep := by
  have hf_metric :
      f ∈ (data.metricFiber p).carrier :=
    data.fiber_subset_metric p hf
  have hcenter_metric :
      data.assignment.center p ∈
        (data.metricFiber p).carrier :=
    data.center_mem_metric p
  have hf_ball :
      f ∈ c2Ball (data.metricCenter p) (data.exactT p) :=
    ((data.certificate p).metric_subset hf_metric).2
  have hcenter_ball :
      data.assignment.center p ∈
        c2Ball (data.metricCenter p) (data.exactT p) :=
    ((data.certificate p).metric_subset hcenter_metric).2
  have hdist :
      c2Distance f (data.assignment.center p) ≤
        2 * data.exactT p := by
    simpa [c2Distance_eq_dist] using
      localAssembly_dist_le_two_mul_of_mem_ball
        hf_ball hcenter_ball
  have hexact_pos : 0 < data.exactT p :=
    hdelta.trans_le (data.certificate p).delta_le_t
  exact hdist.trans (by
    have hrep := data.four_exactT_le_rep p
    linarith)

lemma fiber_card_le_katz_tao
    {baseDelta C_KT : ℝ}
    (hdelta : 0 < delta)
    (hKT :
      data.ambientSource.HasKatzTaoBound baseDelta C_KT)
    (hbaseDelta : baseDelta ≤ tRep)
    (htRep : tRep ≤ 1)
    (p : E) :
    ((data.assignment.fiber p).card : ℝ) ≤
      C_KT * (tRep / baseDelta) := by
  have hsubset :
      (data.assignment.fiber p).carrier ⊆
        data.ambientSource.carrier ∩
          c2Ball (data.assignment.center p) tRep := by
    intro f hf
    refine ⟨data.fiber_subset_ambient p hf, ?_⟩
    rw [mem_c2Ball]
    exact data.fiber_dist_le_representative hdelta p f hf
  have htargetFinite :
      (data.ambientSource.carrier ∩
        c2Ball (data.assignment.center p) tRep).Finite :=
    data.ambientSource.finite.inter_of_left _
  have hcard :
      ((data.assignment.fiber p).carrier.ncard : ℝ) ≤
        ((data.ambientSource.carrier ∩
          c2Ball (data.assignment.center p) tRep).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsubset htargetFinite
  exact hcard.trans
    (hKT.2 (data.assignment.center p) tRep hbaseDelta htRep)

lemma fiber_card_le_katz_tao_all_scales
    {baseDelta C_KT : ℝ}
    (hdelta : 0 < delta)
    (hKT :
      data.ambientSource.HasKatzTaoBound baseDelta C_KT)
    (hbaseDelta : 0 < baseDelta)
    (hC_KT : 0 ≤ C_KT)
    (hbaseDelta_tRep : baseDelta ≤ tRep)
    (p : E) :
    ((data.assignment.fiber p).card : ℝ) ≤
      C_KT * (tRep / baseDelta) := by
  by_cases htRep : tRep ≤ 1
  · exact data.fiber_card_le_katz_tao
      hdelta hKT hbaseDelta_tRep htRep p
  · have hone_tRep : 1 ≤ tRep := le_of_not_ge htRep
    have hcard :
        ((data.assignment.fiber p).card : ℝ) ≤
          (data.ambientSource.card : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard
        (data.fiber_subset_ambient p) data.ambientSource.finite
    have htotal :
        (data.ambientSource.card : ℝ) ≤ C_KT / baseDelta :=
      hKT.1
    have hscale :
        C_KT / baseDelta ≤ C_KT * (tRep / baseDelta) := by
      have hone_scaled :
          1 / baseDelta ≤ tRep / baseDelta :=
        (div_le_div_iff_of_pos_right hbaseDelta).2 hone_tRep
      calc
        C_KT / baseDelta =
            C_KT * (1 / baseDelta) := by ring
        _ ≤ C_KT * (tRep / baseDelta) :=
          mul_le_mul_of_nonneg_left hone_scaled hC_KT
    exact hcard.trans (htotal.trans hscale)

lemma fiber_subset_ambient_cluster
    (hdelta : 0 < delta)
    {center : C2Function} {radius : ℝ}
    (p : E)
    (hcenter :
      c2Distance (data.assignment.center p) center ≤ radius)
    (hradius : tRep + radius ≤ 3 * tRep) :
    (data.assignment.fiber p).carrier ⊆
      (data.ambientSource.cluster center (3 * tRep)).carrier := by
  intro f hf
  refine ⟨data.fiber_subset_ambient p hf, ?_⟩
  rw [mem_c2Ball]
  have hdist :=
    data.fiber_dist_le_representative hdelta p f hf
  have htriangle :
      c2Distance f center ≤
        c2Distance f (data.assignment.center p) +
          c2Distance (data.assignment.center p) center := by
    simpa [c2Distance_eq_dist] using
      dist_triangle f (data.assignment.center p) center
  exact htriangle.trans (by linarith)

lemma fiber_dist_le_six_representative
    (hdelta : 0 < delta)
    (p : E) (f : C2Function)
    (hf : f ∈ (data.assignment.fiber p).carrier) :
    c2Distance f (data.assignment.center p) ≤ 6 * tRep := by
  have hdist :=
    data.fiber_dist_le_representative hdelta p f hf
  have hexact_pos : 0 < data.exactT p :=
    hdelta.trans_le (data.certificate p).delta_le_t
  have htRep_pos : 0 < tRep :=
    lt_of_lt_of_le (by positivity)
      (data.four_exactT_le_rep p)
  linarith

lemma tRep_le_eight_diameter
    (ddata : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (hdelta : 0 < delta) (p : E) :
    tRep ≤ 8 * diameter := by
  have hrep := ddata.rep_le_eight_exactT p
  have hexact := (ddata.certificate p).t_le_diameter
  linarith

lemma fiber_tangency_le_representative
    (p : E) (f : C2Function)
    (hf : f ∈ (data.assignment.fiber p).carrier) :
    tangencyParameterOn data.interval f
        (data.assignment.center p) ≤ DeltaRep := by
  have hf_tangent :
      f ∈ (data.tangencyFiber p).carrier := by
    simpa [data.assignment_fiber p] using hf
  have hparam :
      tangencyParameterOn data.interval f
          (data.tangencyCenter p) ≤ data.exactDelta p := by
    rw [(data.certificate p).tangencyFiber_eq] at hf_tangent
    exact hf_tangent.2
  rw [data.assignment_center p]
  exact hparam.trans (data.exactDelta_le_rep p)

lemma retained_tangency_fiber_lower
    (hdelta : 0 < delta) (p : E) :
    Real.rpow (data.exactT p / diameter) epsilon *
        Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
        (data.mu : ℝ) ≤
      2 * ((data.assignment.fiber p).card : ℝ) := by
  have hmu :
      (data.mu : ℝ) ≤ ((data.source p).card : ℝ) := by
    exact_mod_cast data.mu_le_source p
  have hexactT : 0 < data.exactT p :=
    hdelta.trans_le (data.certificate p).delta_le_t
  have hdiameter : 0 < diameter :=
    hexactT.trans_le (data.certificate p).t_le_diameter
  have hexactDelta : 0 < data.exactDelta p :=
    hdelta.trans_le (data.certificate p).delta_le_Delta
  have hmetricFactor :
      0 ≤ Real.rpow (data.exactT p / diameter) epsilon :=
    Real.rpow_nonneg (div_nonneg hexactT.le hdiameter.le) _
  have htangencyFactor :
      0 ≤ Real.rpow
        (data.exactDelta p / (4 * data.exactT p)) eta :=
    Real.rpow_nonneg (div_nonneg hexactDelta.le (by positivity)) _
  have hmetric :
      Real.rpow (data.exactT p / diameter) epsilon *
          (data.mu : ℝ) ≤
        ((data.metricFiber p).card : ℝ) := by
    calc
      Real.rpow (data.exactT p / diameter) epsilon *
          (data.mu : ℝ) ≤
          Real.rpow (data.exactT p / diameter) epsilon *
            ((data.source p).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hmu hmetricFactor
      _ ≤ ((data.metricFiber p).card : ℝ) :=
        (data.certificate p).metric_retention
  have htangency :
      Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
          (Real.rpow (data.exactT p / diameter) epsilon *
            (data.mu : ℝ)) ≤
        2 * ((data.tangencyFiber p).card : ℝ) := by
    calc
      Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
          (Real.rpow (data.exactT p / diameter) epsilon *
            (data.mu : ℝ)) ≤
          Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
            ((data.metricFiber p).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hmetric htangencyFactor
      _ ≤ 2 * ((data.tangencyFiber p).card : ℝ) :=
        (data.certificate p).tangency_retention
  rw [data.assignment_fiber p]
  calc
    Real.rpow (data.exactT p / diameter) epsilon *
        Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
        (data.mu : ℝ) =
      Real.rpow (data.exactDelta p / (4 * data.exactT p)) eta *
        (Real.rpow (data.exactT p / diameter) epsilon *
          (data.mu : ℝ)) := by ring
    _ ≤ 2 * ((data.tangencyFiber p).card : ℝ) := htangency

lemma retained_fiber_lower_at_representatives
    (hdelta : 0 < delta) (p : E) :
    Real.rpow (tRep / (8 * diameter)) epsilon *
        Real.rpow (DeltaRep / (2 * tRep)) eta *
        (data.mu : ℝ) ≤
      2 * ((data.assignment.fiber p).card : ℝ) := by
  have hexactT : 0 < data.exactT p :=
    hdelta.trans_le (data.certificate p).delta_le_t
  have hdiameter : 0 < diameter :=
    hexactT.trans_le (data.certificate p).t_le_diameter
  have hexactDelta : 0 < data.exactDelta p :=
    hdelta.trans_le (data.certificate p).delta_le_Delta
  have htRep : 0 < tRep := data.tRep_pos
  have hDeltaRep : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hmetric_ratio :
      tRep / (8 * diameter) ≤ data.exactT p / diameter := by
    calc
      tRep / (8 * diameter) = (tRep / 8) / diameter := by ring
      _ ≤ data.exactT p / diameter := by
        apply (div_le_div_iff_of_pos_right hdiameter).2
        have hrep := data.rep_le_eight_exactT p
        linarith
  have htangency_ratio :
      DeltaRep / (2 * tRep) ≤
        data.exactDelta p / (4 * data.exactT p) := by
    have hfirst :
        DeltaRep / (2 * tRep) ≤ data.exactDelta p / tRep := by
      calc
        DeltaRep / (2 * tRep) = (DeltaRep / 2) / tRep := by ring
        _ ≤ data.exactDelta p / tRep := by
          apply (div_le_div_iff_of_pos_right htRep).2
          have hrep := data.repDelta_le_two_exactDelta p
          linarith
    have hsecond :
        data.exactDelta p / tRep ≤
          data.exactDelta p / (4 * data.exactT p) := by
      apply div_le_div_of_nonneg_left hexactDelta.le
        (by positivity)
      exact data.four_exactT_le_rep p
    exact hfirst.trans hsecond
  have hmetric_rpow :
      Real.rpow (tRep / (8 * diameter)) epsilon ≤
        Real.rpow (data.exactT p / diameter) epsilon :=
    Real.rpow_le_rpow (by positivity) hmetric_ratio data.epsilon_pos.le
  have htangency_rpow :
      Real.rpow (DeltaRep / (2 * tRep)) eta ≤
        Real.rpow
          (data.exactDelta p / (4 * data.exactT p)) eta :=
    Real.rpow_le_rpow (by positivity) htangency_ratio data.eta_pos.le
  have hmu_nonneg : 0 ≤ (data.mu : ℝ) := by positivity
  have hmetric_exact_nonneg :
      0 ≤ Real.rpow (data.exactT p / diameter) epsilon :=
    Real.rpow_nonneg (by positivity) _
  have htangency_rep_nonneg :
      0 ≤ Real.rpow (DeltaRep / (2 * tRep)) eta :=
    Real.rpow_nonneg (by positivity) _
  calc
    Real.rpow (tRep / (8 * diameter)) epsilon *
          Real.rpow (DeltaRep / (2 * tRep)) eta *
          (data.mu : ℝ) ≤
        Real.rpow (data.exactT p / diameter) epsilon *
          Real.rpow (DeltaRep / (2 * tRep)) eta *
          (data.mu : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmetric_rpow
          htangency_rep_nonneg) hmu_nonneg
    _ ≤
        Real.rpow (data.exactT p / diameter) epsilon *
          Real.rpow
            (data.exactDelta p / (4 * data.exactT p)) eta *
          (data.mu : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htangency_rpow
          hmetric_exact_nonneg) hmu_nonneg
    _ ≤ 2 * ((data.assignment.fiber p).card : ℝ) :=
      data.retained_tangency_fiber_lower hdelta p

lemma exists_uniform_fiber_count_at_representatives
    (hdelta : 0 < delta) :
    ∃ q : ℕ,
      0 < q ∧
      (∀ p : E, q ≤ (data.assignment.fiber p).card) ∧
      Real.rpow (tRep / (8 * diameter)) epsilon *
          Real.rpow (DeltaRep / (2 * tRep)) eta *
          (data.mu : ℝ) <
        4 * ((q : ℝ) + 1) := by
  let lower : ℝ :=
    Real.rpow (tRep / (8 * diameter)) epsilon *
      Real.rpow (DeltaRep / (2 * tRep)) eta *
      (data.mu : ℝ)
  let safeLower : ℝ := max lower 0
  let q : ℕ := max 1 (Nat.floor (safeLower / 4))
  have hsafe_nonneg : 0 ≤ safeLower := by
    exact le_max_right _ _
  have hfloor_real :
      ((Nat.floor (safeLower / 4) : ℕ) : ℝ) ≤ safeLower / 4 :=
    Nat.floor_le (by positivity)
  have hfloor_le_card (p : E) :
      Nat.floor (safeLower / 4) ≤ (data.assignment.fiber p).card := by
    have hlower :=
      data.retained_fiber_lower_at_representatives hdelta p
    change lower ≤ 2 * ((data.assignment.fiber p).card : ℝ) at hlower
    have hsafe :
        safeLower ≤ 2 * ((data.assignment.fiber p).card : ℝ) := by
      apply max_le
      · exact hlower
      · positivity
    have hdiv :
        safeLower / 4 ≤ ((data.assignment.fiber p).card : ℝ) := by
      have hcard_nonneg :
          0 ≤ ((data.assignment.fiber p).card : ℝ) := by positivity
      linarith
    exact_mod_cast hfloor_real.trans hdiv
  have hq_pos : 0 < q := by
    dsimp only [q]
    omega
  have hq_le_card (p : E) :
      q ≤ (data.assignment.fiber p).card := by
    dsimp only [q]
    apply max_le
    · exact data.fiber_card_pos hdelta p
    · exact hfloor_le_card p
  have hfloor_upper :
      safeLower / 4 <
        ((Nat.floor (safeLower / 4) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one (safeLower / 4)
  have hfloor_le_q :
      Nat.floor (safeLower / 4) ≤ q := by
    dsimp only [q]
    exact le_max_right _ _
  have hfloor_le_q_real :
      ((Nat.floor (safeLower / 4) : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hfloor_le_q
  refine ⟨q, hq_pos, hq_le_card, ?_⟩
  have hlower_safe : lower ≤ safeLower := le_max_left _ _
  dsimp only [lower] at hlower_safe ⊢
  linarith

end DyadicFineAssignmentData

end Kakeya.Cinematic
