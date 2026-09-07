module

/-
  MainProof_G.lean

  Radial bootstrapping main proof using G-intersection bad tubes.
-/

public import MyLeanRepo.RadialBootstrapping.WellBehavedTubes
public import MyLeanRepo.RadialBootstrapping.HBarGMeasurable
public import MyLeanRepo.RadialBootstrapping.HBarMeasurable
public import MyLeanRepo.RadialBootstrapping.MeasureHelpers
public import MyLeanRepo.RadialBootstrapping.Constants
public import MyLeanRepo.RadialBootstrapping.NegationHelpers
public import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- HBarG over dyadic scales. -/
def HBarG_dyadic (ν₂ : Measure Point)
    (G : Set (Point × Point)) (K' σ τ : ℝ) : Set (Point × Point) :=
  {p | ∃ (r : ℝ), r ∈ Dyadic ∧ p ∈ HBarG_r_strict ν₂ G K' σ τ r}

/-- H = G ∩ HBarG_dyadic. -/
def HG_dyadic (G : Set (Point × Point))
    (ν₂ : Measure Point) (K' σ τ : ℝ) : Set (Point × Point) :=
  G ∩ HBarG_dyadic ν₂ G K' σ τ

/-- HBarG_dyadic is measurable (countable union of measurable sets). -/
lemma HBarG_dyadic_measurable
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (K' σ τ : ℝ) (hK'_nonneg : 0 ≤ K') (hστ_nonneg : 0 ≤ σ + τ) :
    MeasurableSet (HBarG_dyadic ν₂ G K' σ τ) := by
  have h_dyadic_countable : Set.Countable (Dyadic : Set ℝ) := by
    have h : (Dyadic : Set ℝ) = Set.range (fun n : ℤ => (2 : ℝ) ^ n) := by
      ext x; simp [Dyadic] <;> constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn.symm⟩
    exact h ▸ Set.countable_range _
  have h_eq : HBarG_dyadic ν₂ G K' σ τ = ⋃ r ∈ (Dyadic : Set ℝ), HBarG_r_strict ν₂ G K' σ τ r := by
    ext p; simp [HBarG_dyadic, Set.mem_iUnion₂] <;> tauto
  rw [h_eq]
  exact MeasurableSet.biUnion h_dyadic_countable (fun r hr =>
    HBarG_r_strict_measurable ν₂ G hG_meas K' σ τ r (by
      rcases hr with ⟨n, rfl⟩
      positivity) hK'_nonneg hστ_nonneg)

/-- If thin tubes fails, then G ∩ HBarG_dyadic(K'') has measure ≥ c,
    where K'' = K' / 2^(σ+τ).

    Key idea: E = G \ HBarG_dyadic(K'') satisfies the fiber bound with constant K'.
    For any tube at scale s, pick dyadic r ∈ [s, 2s). If the tube is K'-bad at s,
    it is K''-bad at r, hence in HBarG_dyadic, so E ∩ tube = ∅. -/
lemma bad_set_measure_G
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (K' σ τ c : ℝ)
    (hK' : 1 ≤ K') (hστ : 0 < σ + τ) (hc_pos : 0 < c) (hc3_lt_one : 3 * c < 1)
    (hG_measure : (ν₁.prod ν₂) G ≥ ENNReal.ofReal (1 - 2 * c))
    (h_not_thin : ¬ HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂) :
    let K'' := K' / (2 : ℝ) ^ (σ + τ)
    (ν₁.prod ν₂) (G ∩ HBarG_dyadic ν₂ G K'' σ τ) ≥ ENNReal.ofReal c := by
  let K'' : ℝ := K' / (2 : ℝ) ^ (σ + τ)
  let HBarG := HBarG_dyadic ν₂ G K'' σ τ
  have hK''_nonneg : 0 ≤ K'' := by
    dsimp only [K'']
    apply div_nonneg <;> positivity
  have hστ_nonneg : 0 ≤ σ + τ := by linarith
  have hHBarG_meas : MeasurableSet HBarG :=
    HBarG_dyadic_measurable ν₂ G hG_meas K'' σ τ hK''_nonneg hστ_nonneg
  let E : Set (Point × Point) := G \ HBarG
  have hE_meas : MeasurableSet E := hG_meas.diff hHBarG_meas
  -- Fiber bound for E with constant K'
  have h_fiber_bound : ∀ (b₁ : Point), b₁ ∈ (ν₁ : Measure Point).support →
      ∀ (ℓ : AffineSubspace ℝ Point), b₁ ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ (s : ℝ), 0 < s →
          ν₂ {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ E} ≤
            Real.toNNReal (K' * Real.rpow s (σ + τ)) := by
    intro b₁ _ ℓ hb₁ℓ hfin s hs
    have hK'_nonneg : 0 ≤ K' := by linarith
    have h_val_nonneg : 0 ≤ K' * Real.rpow s (σ + τ) := mul_nonneg hK'_nonneg (Real.rpow_nonneg (by linarith) _)
    by_cases h_bad : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} >
        ENNReal.ofReal (K' * Real.rpow s (σ + τ))
    · -- Tube is K'-bad at scale s: round up to dyadic r ∈ [s, 2s)
      rcases dyadic_enlargement σ τ K' s hστ hs (by linarith) with ⟨r, hr_dyad, hrs_le, hrl, h_mass_ineq⟩
      have hr_pos : 0 < r := by linarith
      have h1 : Metric.thickening s (ℓ : Set Point) ⊆ Metric.thickening r (ℓ : Set Point) :=
        Metric.thickening_mono hrs_le (ℓ : Set Point)
      have h2 : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} ≥
          (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} :=
        measure_mono (fun z hz => ⟨h1 hz.1, hz.2⟩)
      have hK''_pos : 0 < K'' := by
        dsimp only [K'']; apply div_pos <;> positivity
      have h_rpow_pos : 0 < Real.rpow r (σ + τ) := Real.rpow_pos_of_pos hr_pos (σ + τ)
      have h_val_pos : 0 < K'' * Real.rpow r (σ + τ) := mul_pos hK''_pos h_rpow_pos
      have h3 : K'' * Real.rpow r (σ + τ) ≤ K' * Real.rpow s (σ + τ) := by
        simpa [K''] using h_mass_ineq
      have h4 : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} >
          ENNReal.ofReal (K'' * Real.rpow r (σ + τ)) := by
        calc _ ≥ (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} := h2
             _ > ENNReal.ofReal (K' * Real.rpow s (σ + τ)) := h_bad
             _ ≥ ENNReal.ofReal (K'' * Real.rpow r (σ + τ)) := by
               exact ENNReal.ofReal_le_ofReal h3
      have h_in_HBarG : ∀ (b₂ : Point), b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G →
          (b₁, b₂) ∈ HBarG := by
        intro b₂ hb₂
        exact ⟨r, hr_dyad, ℓ, ⟨hb₁ℓ, hfin, h4⟩, h1 hb₂.1⟩
      have h_empty : {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ E} = ∅ := by
        ext b₂
        simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false]
        intro h
        have hG : (b₁, b₂) ∈ G := h.2.1
        have h_not : (b₁, b₂) ∉ HBarG := h.2.2
        exact h_not (h_in_HBarG b₂ ⟨h.1, hG⟩)
      rw [h_empty]; simp [h_val_nonneg]
    · -- Not bad: bound by G-intersection
      have h_le : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} ≤
          ENNReal.ofReal (K' * Real.rpow s (σ + τ)) := le_of_not_gt h_bad
      have h_sub : {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ E} ⊆
          {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ G} := by
        intro b₂ hb₂; exact ⟨hb₂.1, hb₂.2.1⟩
      have h6 : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ E} ≤
          ENNReal.ofReal (K' * Real.rpow s (σ + τ)) :=
        le_trans (measure_mono h_sub) h_le
      let A := {b₂ | b₂ ∈ Metric.thickening s (ℓ : Set Point) ∧ (b₁, b₂) ∈ E}
      have h8 : (↑(ν₂ A) : ENNReal) = (ν₂ : Measure Point) A :=
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ A
      have h9 : (↑(ν₂ A) : ENNReal) ≤ ENNReal.ofReal (K' * Real.rpow s (σ + τ)) := by
        rw [h8]; exact h6
      have h10 : (↑(ν₂ A) : ENNReal) ≤ ↑(Real.toNNReal (K' * Real.rpow s (σ + τ))) := by
        have h11 : ENNReal.ofReal (K' * Real.rpow s (σ + τ)) = ↑(Real.toNNReal (K' * Real.rpow s (σ + τ))) := by
          simp [ENNReal.ofReal]
        rw [h11] at h9
        exact h9
      have h_iff : (↑(ν₂ A) : ENNReal) ≤ ↑(Real.toNNReal (K' * Real.rpow s (σ + τ))) ↔
          ν₂ A ≤ Real.toNNReal (K' * Real.rpow s (σ + τ)) := by exact ENNReal.coe_le_coe
      have h12 : ν₂ A ≤ Real.toNNReal (K' * Real.rpow s (σ + τ)) := h_iff.mp h10
      exact h12
  -- E cannot have measure ≥ 1-3c
  have hβ : 0 ≤ σ + τ := by linarith
  have hc : (3 * c) ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hE_lt : (ν₁.prod ν₂) E < ENNReal.ofReal (1 - 3 * c) := by
    by_contra h
    have h9 : 1 - ENNReal.ofReal (3 * c) = ENNReal.ofReal (1 - 3 * c) := by
      rw [ENNReal.ofReal_sub] <;> norm_num <;> linarith
    have hE_ge : (ν₁.prod ν₂) E ≥ 1 - ENNReal.ofReal (3 * c) := by
      rw [h9]
      exact not_lt.mp h
    rcases not_hasMeasureThinTubes hβ hK' hc h_not_thin E hE_meas hE_ge with ⟨x, ℓ, r, hxl, hfin, hr, hviol⟩
    let A := {b₂ : Point | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ E}
    have h1_pos : 0 < K' * Real.rpow r (σ + τ) := by
      have hK'_pos : 0 < K' := by linarith
      have hrpow_pos : 0 < Real.rpow r (σ + τ) := Real.rpow_pos_of_pos hr (σ + τ)
      exact mul_pos hK'_pos hrpow_pos
    have hA_pos : 0 < ν₂ A := lt_trans (Real.toNNReal_pos.mpr h1_pos) hviol
    have hA_nonempty : Set.Nonempty A := by
      by_contra h5
      have h_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h5
      rw [h_empty] at hA_pos; simpa using hA_pos
    rcases hA_nonempty with ⟨y, hy⟩
    have h_bad_enreal : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ G} >
        ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := by
      have h_coe : (↑(ν₂ A) : ENNReal) = (ν₂ : Measure Point) A :=
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ A
      have h_gt : (↑(ν₂ A) : ENNReal) > ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := by
        let threshold_nn : NNReal := Real.toNNReal (K' * Real.rpow r (σ + τ))
        have hviol_nn : ν₂ A > threshold_nn := hviol
        have h : (↑threshold_nn : ENNReal) < (↑(ν₂ A) : ENNReal) := by exact_mod_cast hviol_nn
        have h9 : (↑threshold_nn : ENNReal) = ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := by
          unfold ENNReal.ofReal; rfl
        rw [h9] at h; exact h
      rw [h_coe] at h_gt
      have h10 : (ν₂ : Measure Point) A ≤ (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ G} :=
        measure_mono (fun z hz => ⟨hz.1, hz.2.1⟩)
      exact h_gt.trans_le h10
    -- This tube is K'-bad at scale r, so it should be in HBarG_dyadic
    -- But r might not be dyadic. Round up to a dyadic scale.
    rcases dyadic_enlargement σ τ K' r hστ hr (by linarith) with ⟨r', hr'_dyad, hrr'_le, hr'_lt, h_mass_ineq⟩
    have hr'_pos : 0 < r' := by linarith
    have h11 : Metric.thickening r (ℓ : Set Point) ⊆ Metric.thickening r' (ℓ : Set Point) :=
      Metric.thickening_mono hrr'_le (ℓ : Set Point)
    have h12 : (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r' (ℓ : Set Point) ∧ (x, b₂) ∈ G} >
        ENNReal.ofReal (K'' * Real.rpow r' (σ + τ)) := by
      have h13 : K'' * Real.rpow r' (σ + τ) ≤ K' * Real.rpow r (σ + τ) := by
        simpa [K''] using h_mass_ineq
      have h14 : {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ G} ⊆
          {b₂ | b₂ ∈ Metric.thickening r' (ℓ : Set Point) ∧ (x, b₂) ∈ G} := by
        intro z hz
        exact ⟨h11 hz.1, hz.2⟩
      have h_val_pos : 0 < K'' * Real.rpow r' (σ + τ) := by
        have hK''_pos : 0 < K'' := by dsimp only [K'']; apply div_pos <;> positivity
        have h_rpow_pos : 0 < Real.rpow r' (σ + τ) := Real.rpow_pos_of_pos hr'_pos (σ + τ)
        exact mul_pos hK''_pos h_rpow_pos
      calc _ ≥ (ν₂ : Measure Point) {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ G} :=
          measure_mono h14
           _ > ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := h_bad_enreal
           _ ≥ ENNReal.ofReal (K'' * Real.rpow r' (σ + τ)) := by
             exact ENNReal.ofReal_le_ofReal h13
    have h14 : (x, y) ∈ HBarG := ⟨r', hr'_dyad, ℓ, ⟨hxl, hfin, h12⟩, h11 hy.1⟩
    have h15 : (x, y) ∉ HBarG := hy.2.2
    exact h15 h14
  -- Derive μ(G ∩ HBarG) ≥ c
  let μ : Measure (Point × Point) := (ν₁.prod ν₂ : Measure (Point × Point))
  have h_disj : Disjoint (G ∩ HBarG) E := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2.2 hz1.2
  have h_union : G = (G ∩ HBarG) ∪ E := by
    ext z
    simp [E, Set.mem_inter_iff] <;> tauto
  have h_inter_meas : MeasurableSet (G ∩ HBarG) :=
    MeasurableSet.inter hG_meas hHBarG_meas
  have h_union_meas : μ ((G ∩ HBarG) ∪ E) = μ (G ∩ HBarG) + μ E := by exact measure_union h_disj hE_meas
  have h_eq : μ G = μ (G ∩ HBarG) + μ E := by
    have hG_eq : μ G = μ ((G ∩ HBarG) ∪ E) :=
    congr_arg μ h_union
    rw [hG_eq]
    exact h_union_meas
  have hG_enn : μ G ≥ ENNReal.ofReal (1 - 2 * c) := by
    have h_coe : μ G = ↑((ν₁.prod ν₂) G) := by simp [μ] <;> rfl
    rw [h_coe]; exact hG_measure
  have hE_lt_enn : μ E < ENNReal.ofReal (1 - 3 * c) := by
    have h_coe : μ E = ↑((ν₁.prod ν₂) E) := by simp [μ] <;> rfl
    rw [h_coe]; exact hE_lt
  have h_pos1 : 0 ≤ 1 - 2 * c := by linarith
  have h_pos2 : 0 ≤ 1 - 3 * c := by linarith
  have h_pos3 : 0 ≤ c := by linarith
  have h_sum : ENNReal.ofReal (1 - 2 * c) = ENNReal.ofReal c + ENNReal.ofReal (1 - 3 * c) := by
    rw [← ENNReal.ofReal_add h_pos3 h_pos2] <;> ring_nf
  have h_main : μ (G ∩ HBarG) + μ E ≥ ENNReal.ofReal c + ENNReal.ofReal (1 - 3 * c) := by
    calc μ (G ∩ HBarG) + μ E
      = μ G := h_eq.symm
    _ ≥ ENNReal.ofReal (1 - 2 * c) := hG_enn
    _ = ENNReal.ofReal c + ENNReal.ofReal (1 - 3 * c) := h_sum
  have hE_ne_top : μ E ≠ ⊤ := ne_top_of_lt hE_lt_enn
  have h_final : μ (G ∩ HBarG) ≥ ENNReal.ofReal c := by
    by_contra h
    have h_lt : μ (G ∩ HBarG) < ENNReal.ofReal c := not_le.mp h
    have h_comb : μ (G ∩ HBarG) + μ E < ENNReal.ofReal c + μ E :=
      ENNReal.add_lt_add_right hE_ne_top h_lt
    have hE_le : μ E ≤ ENNReal.ofReal (1 - 3 * c) := hE_lt_enn.le
    have h4 : μ (G ∩ HBarG) + μ E < ENNReal.ofReal c + ENNReal.ofReal (1 - 3 * c) := by
      calc μ (G ∩ HBarG) + μ E
        < ENNReal.ofReal c + μ E := h_comb
      _ ≤ ENNReal.ofReal c + ENNReal.ofReal (1 - 3 * c) := by gcongr
    exact not_le.mpr h4 h_main
  have h_coe_out : μ (G ∩ HBarG) = ↑((ν₁.prod ν₂) (G ∩ HBarG)) := by
    simp [μ] <;> rfl
  have h_goal : ↑((ν₁.prod ν₂) (G ∩ HBarG)) ≥ ENNReal.ofReal c := by
    rw [←h_coe_out]; exact h_final
  exact h_goal

end RadialBootstrapping
