module

/-
Standalone proof of relative subset energy bound for Endgame v3.

Shows: if μE = uniformMeasureOn E and μE3 = uniformMeasureOn E3fin,
with E3fin ⊆ E and |E3fin| ≥ δ^(3*rho_sel) * |E|,
then for any measurable projection f:
  I(π_f μE3) ≤ δ^{-6*rho_sel} · I(π_f μE)

Uses rieszEnergy_subset_uniform_delta_bound from RieszEnergyMonotonicity.
-/

public import MyLeanRepo.Energy.RieszEnergyMonotonicity
public import MyLeanRepo.ProductLikeIncidence.NormalizationHelpers
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Finset

namespace ProductLikeIncidence.ProductReduction

/-- A finite sum of normalized dirac measures equals `uniformMeasureOn`. -/
lemma uniform_measure_eq_dirac_sum {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (E : Finset α) (hE_nonempty : E.Nonempty) :
    uniformMeasureOn E = ∑ p ∈ E, (1 / (E.card : ENNReal)) • Measure.dirac p := by
  have hE_pos : 0 < E.card := Finset.Nonempty.card_pos hE_nonempty
  have h_ae : ∀ᵐ (x : α) ∂(uniformMeasureOn E), x ∈ E := by
    have h1 : ∀ᵐ (x : α) ∂(Measure.count.restrict (E : Set α)), x ∈ E :=
      MeasureTheory.ae_restrict_mem (Finset.measurableSet E)
    have h_ac : uniformMeasureOn E ≪ Measure.count.restrict (E : Set α) := by
      apply Measure.AbsolutelyContinuous.mk
      intro s hs hnull
      simp [uniformMeasureOn, hnull]
      <;> exact zero_mul _
    exact h_ac h1
  have h_eq : uniformMeasureOn E = ∑ p ∈ E, (uniformMeasureOn E) {p} • Measure.dirac p :=
    (Measure.ae_mem_finset_iff (s := E)).mp h_ae
  rw [h_eq]
  apply Finset.sum_congr rfl
  intro p hp
  have h_single : (uniformMeasureOn E) {p} = (1 / (E.card : ENNReal)) := by
    rw [uniformMeasureOn_apply E hE_nonempty {p} (MeasurableSet.singleton p)]
    have h_inter : (E : Set α) ∩ {p} = {p} := by
      ext x; simp [hp] <;> tauto
    rw [h_inter]
    <;> simp [hE_pos.ne'] <;> ring
  rw [h_single]

/-- μE3 defined as normalized dirac sum equals `uniformMeasureOn E3fin`. -/
lemma muE3_eq_uniform {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {E3 : Set α} (E3fin : Finset α) (hE3_nonempty : E3fin.Nonempty)
    (hE3fin_coe : (E3fin : Set α) = E3) :
    (∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) =
    uniformMeasureOn E3fin := by
  have h_card : ENat.toENNReal E3.encard = (E3fin.card : ENNReal) := by
    rw [← hE3fin_coe] <;> simp
  have h_main : (∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) =
      ∑ p ∈ E3fin, (1 / (E3fin.card : ENNReal)) • Measure.dirac p := by
    congr with p
    <;> rw [h_card]
  rw [h_main]
  exact (uniform_measure_eq_dirac_sum E3fin hE3_nonempty).symm

/-- The support of `uniformMeasureOn E` is exactly the coercion of `E`. -/
lemma uniformMeasureOn_support {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [T1Space α] [MeasurableSingletonClass α]
    (E : Finset α) (hE_nonempty : E.Nonempty) :
    (uniformMeasureOn E).support = (E : Set α) := by
  have h_card_pos : 0 < E.card := Finset.Nonempty.card_pos hE_nonempty
  have h_ne_zero : (E.card : ENNReal) ≠ 0 := by exact_mod_cast h_card_pos.ne'
  have h_ne_top : (E.card : ENNReal) ≠ ⊤ := by simp
  have h_fin : (E : Set α).Finite := by simp
  have h_closed : IsClosed (E : Set α) := h_fin.isClosed
  have h1 : (uniformMeasureOn E).support ⊆ (E : Set α) := by
    intro x hx
    by_contra h_notin
    have h_nhds : (E : Set α)ᶜ ∈ nhds x := h_closed.isOpen_compl.mem_nhds h_notin
    have h_compl_open : IsOpen ((E : Set α)ᶜ) := h_closed.isOpen_compl
    have h_compl_meas : MeasurableSet ((E : Set α)ᶜ) := h_compl_open.measurableSet
    have h_meas : (uniformMeasureOn E) ((E : Set α)ᶜ) = 0 := by
      rw [uniformMeasureOn_apply E hE_nonempty ((E : Set α)ᶜ) h_compl_meas] <;> simp
    have h_not_supp : x ∉ (uniformMeasureOn E).support :=
      Measure.notMem_support_iff_exists.mpr ⟨_, h_nhds, h_meas⟩
    exact h_not_supp hx
  have h2 : (E : Set α) ⊆ (uniformMeasureOn E).support := by
    intro p hp
    have h3 : (uniformMeasureOn E) {p} > 0 := by
      rw [uniformMeasureOn_apply E hE_nonempty {p} (MeasurableSet.singleton p)]
      have h_inter : (E : Set α) ∩ {p} = {p} := by ext z; simp [hp] <;> tauto
      rw [h_inter]
      simp [h_ne_zero] <;> exact ENNReal.div_pos one_ne_zero h_ne_top
    by_contra h4
    rcases Measure.notMem_support_iff_exists.mp h4 with ⟨U, hU_nhds, hU_zero⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hpV⟩
    have hV_zero : (uniformMeasureOn E) V = 0 := by
      have h : (uniformMeasureOn E) V ≤ (uniformMeasureOn E) U := measure_mono hV_sub
      rw [hU_zero] at h; exact le_zero_iff.mp h
    have h6 : (uniformMeasureOn E) {p} ≤ (uniformMeasureOn E) V :=
      measure_mono (fun x hx => hx ▸ hpV)
    rw [hV_zero] at h6
    have h7 : (uniformMeasureOn E) {p} = 0 := by simpa using h6
    rw [h7] at h3; simpa using h3
  exact Set.Subset.antisymm h1 h2

/-- Type-specialized version of `uniformMeasureOn_support` for the Euclidean plane.
    This avoids expensive typeclass resolution at the call site. -/
lemma uniformMeasureOn_support_plane
    (E : Finset (EuclideanSpace ℝ (Fin 2))) (hE_nonempty : E.Nonempty) :
    (uniformMeasureOn E).support = (E : Set (EuclideanSpace ℝ (Fin 2))) :=
  uniformMeasureOn_support E hE_nonempty

/-- Fully wrapped support proof for the endgame: given μE3 = uniformMeasureOn E3fin
    and (E3fin : Set _) = E3, conclude μE3.support = E3. All typeclass resolution
    happens here, not at the call site. -/
lemma endgame_muE3_support
    (E3fin : Finset (EuclideanSpace ℝ (Fin 2)))
    (hE3fin_nonempty : E3fin.Nonempty)
    (E3 : Set (EuclideanSpace ℝ (Fin 2)))
    (hE3fin_coe : (E3fin : Set (EuclideanSpace ℝ (Fin 2))) = E3)
    (μE3 : Measure (EuclideanSpace ℝ (Fin 2)))
    (hμE3_eq : μE3 = uniformMeasureOn E3fin) :
    μE3.support = E3 := by
  rw [hμE3_eq]
  have h : (uniformMeasureOn E3fin).support = (E3fin : Set (EuclideanSpace ℝ (Fin 2))) :=
    uniformMeasureOn_support_plane E3fin hE3fin_nonempty
  rw [h]
  exact hE3fin_coe

/-- Relative subset energy bound: uniform measure on E3 ⊆ E has
    Riesz energy ≤ (|E|/|E3|)² times energy on E, and with
    |E3| ≥ δ^(3*rho_sel)·|E|, this gives δ^{-6*rho_sel} factor. -/
lemma relative_subset_energy_bound
    {δ κ0 rho_sel : ℝ} (hδ_pos : 0 < δ) (hκ0_pos : 0 < κ0) (hrho_sel_pos : 0 < rho_sel)
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MetricSpace β] [MeasurableSpace β]
    {E E3fin : Finset α} (hE3_sub : E3fin ⊆ E) (hE3_nonempty : E3fin.Nonempty)
    (f : α → β) (hf : Measurable f)
    (h_retention : (E3fin.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal)) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map f (uniformMeasureOn E3fin)) ≤
    ENNReal.ofReal (δ ^ (-(6 * rho_sel))) *
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map f (uniformMeasureOn E)) := by
  -- Convert ENNReal retention to Real retention
  have hE_pos : 0 < E.card := Finset.Nonempty.card_pos (hE3_nonempty.mono hE3_sub)
  have hE3_pos : 0 < E3fin.card := Finset.Nonempty.card_pos hE3_nonempty
  have h_pos_rpow : 0 ≤ δ ^ (3 * rho_sel) := by positivity
  have hE_coe : (E.card : ENNReal) = ENNReal.ofReal (E.card : ℝ) := by simp
  have h_retention_real : (E3fin.card : ℝ) ≥ δ ^ (3 * rho_sel) * (E.card : ℝ) := by
    have h1 : (E3fin.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := h_retention
    rw [hE_coe] at h1
    have h2 : ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENNReal.ofReal (E.card : ℝ) =
        ENNReal.ofReal (δ ^ (3 * rho_sel) * (E.card : ℝ)) := by
      rw [← ENNReal.ofReal_mul h_pos_rpow]
    rw [h2] at h1
    exact_mod_cast h1
  exact rieszEnergy_subset_uniform_delta_bound (α_exp := 2 * κ0) hδ_pos E E3fin hE3_sub hE3_nonempty f hf hrho_sel_pos h_retention_real

/-- Absolute energy bound: combine relative bound with Kaufman threshold.
    If I(π_θ μE) ≤ δ^{-q_bad}, then I(π_θ μE3) ≤ δ^{-(q_bad + 6·rho_sel)}. -/
lemma absolute_subset_energy_bound
    {δ κ0 rho_sel q_bad : ℝ} (hδ_pos : 0 < δ) (hκ0_pos : 0 < κ0) (hrho_sel_pos : 0 < rho_sel) (hq_bad_pos : 0 < q_bad)
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MetricSpace β] [MeasurableSpace β]
    {E E3fin : Finset α} (hE3_sub : E3fin ⊆ E) (hE3_nonempty : E3fin.Nonempty)
    (f : α → β) (hf : Measurable f)
    (h_retention : (E3fin.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal))
    (h_abs_E : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map f (uniformMeasureOn E)) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map f (uniformMeasureOn E3fin)) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) := by
  have h_rel := relative_subset_energy_bound hδ_pos hκ0_pos hrho_sel_pos hE3_sub hE3_nonempty f hf h_retention
  have h_mul : ENNReal.ofReal (δ ^ (-(6 * rho_sel))) * ENNReal.ofReal (δ ^ (-q_bad)) =
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) := by
    have h_pos1 : 0 ≤ δ ^ (-(6 * rho_sel)) := by positivity
    rw [← ENNReal.ofReal_mul h_pos1]
    have h_rpow : δ ^ (-(6 * rho_sel)) * δ ^ (-q_bad) = δ ^ (-(q_bad + 6 * rho_sel)) := by
      have h_eq : δ ^ (-(6 * rho_sel)) * δ ^ (-q_bad) = δ ^ (-(6 * rho_sel) + -q_bad) :=
        (Real.rpow_add (x := δ) hδ_pos (-(6 * rho_sel)) (-q_bad)).symm
      have h_exp : -(6 * rho_sel) + -q_bad = -(q_bad + 6 * rho_sel) := by ring
      rw [h_eq, h_exp]
    rw [h_rpow]
  calc robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map f (uniformMeasureOn E3fin))
    ≤ ENNReal.ofReal (δ ^ (-(6 * rho_sel))) *
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map f (uniformMeasureOn E)) := h_rel
  _ ≤ ENNReal.ofReal (δ ^ (-(6 * rho_sel))) * ENNReal.ofReal (δ ^ (-q_bad)) := by gcongr
  _ = ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) := h_mul

/-- Coordinate energy bound for b3·π_θ2 μE3.
    Uses three_direction_coeffs + coordinate_energy_combined from NormalizationHelpers. -/
lemma coordinate_energy_b3_bound
    {δ κ0 rho_sel rho_sep q_bad : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hκ0_pos : 0 < κ0)
    (hrho_sel_pos : 0 < rho_sel) (hrho_sep_pos : 0 < rho_sep) (hrho_sep_le_one : rho_sep ≤ 1)
    (hq_bad_pos : 0 < q_bad)
    {μE3 : Measure (EuclideanSpace ℝ (Fin 2))} [SFinite μE3]
    {θ1 θ2 θ3 : ℝ}
    (hθ1_in : θ1 ∈ Set.Icc (0 : ℝ) 1) (hθ2_in : θ2 ∈ Set.Icc (0 : ℝ) 1) (hθ3_in : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ rho_sep) (h_sep23 : |θ2 - θ3| ≥ δ ^ rho_sep)
    (h_abs_E2 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))))
    (h_abs_E1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
  let r : ℝ := δ ^ rho_sep
  have hr_pos : 0 < r := by positivity
  have hr_le_one : r ≤ 1 := by
    exact Real.rpow_le_one hδ_pos.le (by linarith) (by linarith)
  rcases three_direction_coeffs hθ1_in hθ2_in hθ3_in h_ord13 h_ord32 h_sep13 h_sep23 hr_pos hr_le_one
    with ⟨b3, a3, hb3_def, ha3_def, hb3_pos, hb3_le_one, hb3_lower, ha3_pos, ha3_le_one, ha3_lower⟩
  let E_abs : ENNReal := ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))
  have h_combined := coordinate_energy_combined (θ3 := θ3) hδ_pos hκ0_pos hr_pos
    (hb3_pos := hb3_pos) (hb3_le_one := hb3_le_one) (hb3_lower := hb3_lower)
    (ha3_pos := ha3_pos) (ha3_le_one := ha3_le_one) (ha3_lower := ha3_lower)
    (E_abs := E_abs) h_abs_E2 h_abs_E1
  have h_main := h_combined.1
  have h_rpow : r ^ (-(2 * κ0)) = δ ^ (-(2 * κ0 * rho_sep)) := by
    dsimp only [r]
    have h_eq_mul : (δ ^ rho_sep) ^ (-(2 * κ0)) = δ ^ (rho_sep * (-(2 * κ0))) :=
      (Real.rpow_mul (x := δ) hδ_pos.le rho_sep (-(2 * κ0))).symm
    rw [h_eq_mul] <;> ring_nf
  rw [h_rpow] at h_main
  have h_final : ENNReal.ofReal (δ ^ (-(2 * κ0 * rho_sep))) * E_abs =
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
    dsimp only [E_abs]
    have h_pos : 0 ≤ δ ^ (-(2 * κ0 * rho_sep)) := by positivity
    rw [← ENNReal.ofReal_mul h_pos]
    have h_rpow2 : δ ^ (-(2 * κ0 * rho_sep)) * δ ^ (-(q_bad + 6 * rho_sel)) =
        δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep)) := by
      have h_eq2 := Real.rpow_add (x := δ) hδ_pos (-(2 * κ0 * rho_sep)) (-(q_bad + 6 * rho_sel))
      have h_sum : -(2 * κ0 * rho_sep) + (-(q_bad + 6 * rho_sel)) = -(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep) := by ring
      rw [h_sum] at h_eq2
      exact h_eq2.symm
    rw [h_rpow2]
  rw [h_final] at h_main
  have h_goal : (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        b3 * (p 0 * θ2 + p 1)) μE3) =
      Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3 := by
    congr with p
    rw [hb3_def]
  rw [h_goal] at h_main
  exact h_main

/-- Coordinate energy bound for a3·π_θ1 μE3 (symmetric to b3 version). -/
lemma coordinate_energy_a3_bound
    {δ κ0 rho_sel rho_sep q_bad : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hκ0_pos : 0 < κ0)
    (hrho_sel_pos : 0 < rho_sel) (hrho_sep_pos : 0 < rho_sep) (hrho_sep_le_one : rho_sep ≤ 1)
    (hq_bad_pos : 0 < q_bad)
    {μE3 : Measure (EuclideanSpace ℝ (Fin 2))} [SFinite μE3]
    {θ1 θ2 θ3 : ℝ}
    (hθ1_in : θ1 ∈ Set.Icc (0 : ℝ) 1) (hθ2_in : θ2 ∈ Set.Icc (0 : ℝ) 1) (hθ3_in : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ rho_sep) (h_sep23 : |θ2 - θ3| ≥ δ ^ rho_sep)
    (h_abs_E2 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))))
    (h_abs_E1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
  let r : ℝ := δ ^ rho_sep
  have hr_pos : 0 < r := by positivity
  have hr_le_one : r ≤ 1 := Real.rpow_le_one hδ_pos.le (by linarith) (by linarith)
  rcases three_direction_coeffs hθ1_in hθ2_in hθ3_in h_ord13 h_ord32 h_sep13 h_sep23 hr_pos hr_le_one
    with ⟨b3, a3, hb3_def, ha3_def, hb3_pos, hb3_le_one, hb3_lower, ha3_pos, ha3_le_one, ha3_lower⟩
  let E_abs : ENNReal := ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))
  have h_combined := coordinate_energy_combined (θ3 := θ3) hδ_pos hκ0_pos hr_pos
    (hb3_pos := hb3_pos) (hb3_le_one := hb3_le_one) (hb3_lower := hb3_lower)
    (ha3_pos := ha3_pos) (ha3_le_one := ha3_le_one) (ha3_lower := ha3_lower)
    (E_abs := E_abs) h_abs_E2 h_abs_E1
  have h_main := h_combined.2
  have h_rpow : r ^ (-(2 * κ0)) = δ ^ (-(2 * κ0 * rho_sep)) := by
    dsimp only [r]
    have h_eq_mul : (δ ^ rho_sep) ^ (-(2 * κ0)) = δ ^ (rho_sep * (-(2 * κ0))) :=
      (Real.rpow_mul (x := δ) hδ_pos.le rho_sep (-(2 * κ0))).symm
    rw [h_eq_mul] <;> ring_nf
  rw [h_rpow] at h_main
  have h_final : ENNReal.ofReal (δ ^ (-(2 * κ0 * rho_sep))) * E_abs =
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
    dsimp only [E_abs]
    have h_pos : 0 ≤ δ ^ (-(2 * κ0 * rho_sep)) := by positivity
    rw [← ENNReal.ofReal_mul h_pos]
    have h_rpow2 : δ ^ (-(2 * κ0 * rho_sep)) * δ ^ (-(q_bad + 6 * rho_sel)) =
        δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep)) := by
      have h_eq2 := Real.rpow_add (x := δ) hδ_pos (-(2 * κ0 * rho_sep)) (-(q_bad + 6 * rho_sel))
      have h_sum : -(2 * κ0 * rho_sep) + (-(q_bad + 6 * rho_sel)) = -(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep) := by ring
      rw [h_sum] at h_eq2
      exact h_eq2.symm
    rw [h_rpow2]
  rw [h_final] at h_main
  have h_goal : (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        a3 * (p 0 * θ1 + p 1)) μE3) =
      Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3 := by
    congr with p
    rw [ha3_def]
  rw [h_goal] at h_main
  exact h_main

end ProductLikeIncidence.ProductReduction
