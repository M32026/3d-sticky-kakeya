import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Integrability of graph-neighborhood multiplicity

The multiplicity function is a finite sum of indicators of bounded open sets,
hence it is bounded and has compact support. Therefore its powers are integrable.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

/-- The graph of a C2Function is bounded. -/
lemma functionGraph_bounded (f : C2Function) : Bornology.IsBounded (functionGraph f) := by
  have h1 : functionGraph f ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-‖f.value‖) ‖f.value‖ := by
    intro p hp
    have hx : p.1 ∈ unitInterval := hp.1
    have hy : p.2 = f ⟨p.1, hx⟩ := hp.2
    have h3 : |f ⟨p.1, hx⟩| ≤ ‖f.value‖ := ContinuousMap.norm_coe_le_norm f.value ⟨p.1, hx⟩
    have h4 : p.2 ∈ Set.Icc (-‖f.value‖) ‖f.value‖ := by
      rw [hy]
      simp only [Set.mem_Icc] <;> exact ⟨by linarith [abs_le.mp h3], by linarith [abs_le.mp h3]⟩
    exact ⟨hx, h4⟩
  have h2 : Bornology.IsBounded (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-‖f.value‖) ‖f.value‖) := by
    apply Bornology.IsBounded.prod
    · exact Metric.isBounded_Icc 0 1
    · exact Metric.isBounded_Icc (-‖f.value‖) ‖f.value‖
  exact h2.subset h1

/-- The δ-neighborhood of a graph is bounded. -/
lemma graphNeighborhood_bounded (f : C2Function) (δ : ℝ) :
    Bornology.IsBounded (graphNeighborhood f δ) :=
  (functionGraph_bounded f).thickening

/-- Multiplicity has compact support. -/
lemma multiplicity_hasCompactSupport (F : FiniteFunctionFamily) (δ : ℝ) :
    HasCompactSupport (multiplicity F δ) := by
  classical
  let sets : Set (Set (ℝ × ℝ)) := (fun f : C2Function => graphNeighborhood f δ) '' F.toFinset
  have hsets_finite : sets.Finite := by
    exact Set.Finite.image _ (Finset.finite_toSet _)
  let S : Set (ℝ × ℝ) := ⋃₀ sets
  have hS_bdd : Bornology.IsBounded S := by
    rw [Bornology.isBounded_sUnion hsets_finite]
    intro s hs
    rcases hs with ⟨f, _, rfl⟩
    exact graphNeighborhood_bounded f δ
  have h1 : Function.support (multiplicity F δ) ⊆ S := by
    intro p hp
    have h2 : ∃ f ∈ F.toFinset, p ∈ graphNeighborhood f δ := by
      by_contra h
      push Not at h
      have h3 : ∀ f ∈ F.toFinset, (graphNeighborhood f δ).indicator (fun _ => (1 : ℝ)) p = 0 := by
        intro f hf
        have h4 : p ∉ graphNeighborhood f δ := h f hf
        rw [Set.indicator_apply, if_neg h4]
      have h5 : multiplicity F δ p = 0 := by
        dsimp only [multiplicity]
        rw [Finset.sum_congr rfl h3]
        <;> simp
      exact hp h5
    rcases h2 with ⟨f, hf, hmem⟩
    exact Set.mem_sUnion_of_mem hmem (Set.mem_image_of_mem _ hf)
  have h3 : Bornology.IsBounded (Function.support (multiplicity F δ)) :=
    hS_bdd.subset h1
  have h4 : IsCompact (closure (Function.support (multiplicity F δ))) :=
    h3.isCompact_closure
  exact h4

/-- Multiplicity is bounded by F.card. -/
lemma multiplicity_bounded (F : FiniteFunctionFamily) (δ : ℝ) :
    ∀ p, |multiplicity F δ p| ≤ (F.card : ℝ) := by
  classical
  intro p
  dsimp only [multiplicity]
  have h1 : 0 ≤ multiplicity F δ p := by
    apply Finset.sum_nonneg
    intro f _
    exact Set.indicator_nonneg (fun _ => by norm_num) _
  have h_card : (F.toFinset.card : ℝ) = (F.card : ℝ) := by
    have h1 : F.toFinset = F.finite.toFinset := by rfl
    have h2 : (F.card : ℕ) = F.carrier.ncard := by rfl
    rw [h1, h2]
    have h3 : F.finite.toFinset.card = F.carrier.ncard := by
      exact (Set.ncard_eq_toFinset_card F.carrier F.finite).symm
    exact_mod_cast h3
  have h2 : multiplicity F δ p ≤ (F.card : ℝ) := by
    calc multiplicity F δ p
      = ∑ f ∈ F.toFinset, (graphNeighborhood f δ).indicator (fun _ => (1 : ℝ)) p := rfl
    _ ≤ ∑ f ∈ F.toFinset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      have h_ind : (graphNeighborhood f δ).indicator (fun _ => (1 : ℝ)) p ≤ 1 := by
        rw [Set.indicator_apply]
        split_ifs <;> norm_num
      exact h_ind
    _ = (F.toFinset.card : ℝ) := by simp
    _ = (F.card : ℝ) := by
      have h : (F.toFinset.card : ℝ) = (F.card : ℝ) := by
        exact_mod_cast h_card
      exact h
  have h3 : -(F.card : ℝ) ≤ multiplicity F δ p := by
    have h4 : (0 : ℝ) ≤ (F.card : ℝ) := by positivity
    linarith [h1]
  exact abs_le.mpr ⟨h3, h2⟩

/-- The 3/2 power of multiplicity is integrable. -/
lemma integrable_multiplicity_rpow (F : FiniteFunctionFamily) (δ : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.rpow (multiplicity F δ p) (3 / 2 : ℝ))
      MeasureTheory.volume := by
  set m : ℝ × ℝ → ℝ := multiplicity F δ with hm_def
  have hcs : HasCompactSupport m := multiplicity_hasCompactSupport F δ
  have hmeas : Measurable m := measurable_multiplicity F δ
  have h_m_nonneg : ∀ p, 0 ≤ m p := by
    intro p; dsimp only [m]
    apply Finset.sum_nonneg; intro f _
    exact Set.indicator_nonneg (fun _ => by norm_num) _
  have h_m_bdd : ∀ p, m p ≤ (F.card : ℝ) := by
    intro p
    exact (abs_le.mp (multiplicity_bounded F δ p)).2
  let C : ENNReal := ENNReal.ofReal (F.card : ℝ)
  have hC_ne_top : C ≠ ⊤ := by simp [C]
  have hbdd : ∀ p, ‖m p‖ₑ ≤ C := by
    intro p
    have hnonneg : 0 ≤ m p := h_m_nonneg p
    have h2 : m p ≤ (F.card : ℝ) := h_m_bdd p
    have h3 : ‖m p‖ₑ = ENNReal.ofReal (m p) := by
      rw [Real.enorm_eq_ofReal hnonneg]
    rw [h3]
    exact ENNReal.ofReal_le_ofReal h2
  have hbdd_ae : ∀ᵐ p ∂MeasureTheory.volume, ‖m p‖ₑ ≤ C := by
    filter_upwards with p
    exact hbdd p
  let q : ENNReal := ENNReal.ofReal (3 / 2 : ℝ)
  have hq_ne_zero : q ≠ 0 := by simp [q] <;> norm_num
  have hq_ne_top : q ≠ ⊤ := by simp [q]
  have hmem : MemLp m q MeasureTheory.volume :=
    HasCompactSupport.memLp_of_enorm_bound hcs hmeas.aestronglyMeasurable hbdd_ae hC_ne_top
  have h_int : Integrable (fun x : ℝ × ℝ => ‖m x‖ ^ q.toReal) MeasureTheory.volume :=
    MemLp.integrable_norm_rpow hmem hq_ne_zero hq_ne_top
  have h_toReal : q.toReal = (3 / 2 : ℝ) := by
    simp [q] <;> norm_num
  have h_eq : (fun x : ℝ × ℝ => ‖m x‖ ^ q.toReal) =ᵐ[MeasureTheory.volume]
      (fun x : ℝ × ℝ => Real.rpow (m x) (3 / 2 : ℝ)) := by
    filter_upwards with x
    have hnonneg : 0 ≤ m x := h_m_nonneg x
    have h1 : ‖m x‖ = m x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [h1, h_toReal]
    <;> rfl
  exact Integrable.congr h_int h_eq

end Kakeya.Cinematic
