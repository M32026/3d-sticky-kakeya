/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.TranslationRefinement

/-!
# Joint multi-scale, multi-parent random-translation refinement

`Kakeya.RandomTranslation.exists_joint_refinement` is the *joint* (multi-scale,
multi-parent) analogue of `Kakeya.RandomTranslation.exists_refinement`.

## Why a joint version is needed

The single-layer theorem produces, for one (scale, parent block)
pair, a random-translation Bad set on `(Fin J → E)` together with a
deterministic refinement `s'`.  In the multi-scale random-translation
argument used in `subStickyFrostmanLemma`/`subStickyFrostmanLemma.perScaleDeltaMax`,
the paper runs the random translations *jointly* across all scales and all
parent tubes:

* **Same scale, all parents share `ω k`.**  At scale `k`, a single family
  `𝓡_k = (ω k j)_{j < J k}` is applied to *every* parent tube
  `T_{ρ_{k-1}}` (paper L145-149).  We must not give each parent its own
  independent translation, otherwise the synthesized child family `T'` is
  not the one in the paper.
* **Across scales, M-fold product event.**  The `M` per-scale conditions
  are combined into one good event on the M-fold product sample space.

A single-layer-only formalization would require `Fin.induction` to
sequentially extract one ω at a time, with each scale's ED / Δ_max output
living in its own sample space.  That blocks the `compareDeltaMaxes`
(paper L138-152) step in the proof of GWZ Lemma 7.5, because that step
uses the joint good event to control accumulated translations
`R_1 ∘ … ∘ R_{m-1}` simultaneously.

This joint version produces:

* a Bad set `Bad ⊆ ∀ k : Fin M, Fin (J k) → E` on the M-fold product;
* a deterministic per-(scale, parent) refinement
  `s' : ∀ k, α k → Finset (ι × Fin (J k))` such that **all `(k, p)`
  postconditions hold simultaneously on the same** `ω ∈ Badᶜ`,
  with all parents at the same scale `k` reusing `ω k`.

## Construction strategy (proof sketch)

The joint theorem is *not* a re-proof of the single-layer statement: it packages
a (scale, parent) family of independent invocations of
`exists_refinement` into one joint event via Mathlib's
`Measure.pi` and the union bound provided by
`Kakeya.HasUniformTranslation.productMeasureIndexed_union_bound`.  In particular:

1. Apply `exists_refinement` once for the chosen `ε`
   (same constant across `(scale, parent)` pairs) to extract `Cε`.
2. Let `N := ∑ l, (P l).card` be the total number of `(scale, parent)`
   sub-events.  For each `k` and each `p ∈ P k`, instantiate the single-layer
   postcondition at scale `(δ k, ρ k, r k, s k p, T k, Tρ k p, J k, A k)`
   with budget `ε_budget / N`.  This yields `Bad k p ⊆ Fin (J k) → E`
   with `productMeasure E E (J k) (Bad k p) ≤ ε_budget / N`.
3. Build the joint Bad set
   `Bad := ⋃ k : Fin M, Function.eval k ⁻¹' (⋃ p ∈ P k, Bad k p)`.
4. Inner union bound (`measure_biUnion_finset_le`) gives the per-scale
   set measure `≤ (P k).card · (ε_budget / N)`; outer
   `productMeasureIndexed_union_bound` then sums to
   `N · (ε_budget / N) = ε_budget`.
5. For `ω ∉ Bad`, project to `ω k := Function.eval k ω`; for every
   `p ∈ P k`, observe `ω k ∉ Bad k p` and invoke the per-`(k, p)`
   deterministic refinement to obtain `s' k p`.  Because all parents at
   scale `k` share the same `ω k`, the synthesized family matches the
   paper's "fix `𝓡_k`, apply to every parent" semantics.

The signature fully encodes the joint specification, and
`subStickyFrostmanLemma` in `Kakeya/Sticky.lean` wires against it. -/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya.RandomTranslation

universe u

set_option maxHeartbeats 820000 in
-- The proof packages many independent calls to `exists_refinement`
-- via `productMeasureIndexed` + a union bound; the large existential output and
-- repeated `Classical.choose_spec` extractions push elaboration past the default
-- maxHeartbeats.
/-- **Joint multi-scale, multi-parent random translation lemma** (GWZ Lemma 7.6).  For `M` scales
`(δ k, ρ k)` with radii `r k`, sample sizes `J k` and a per-scale family of parent tubes, this
produces a single joint Bad set on the `M`-fold product sample space of joint measure `≤ ε_budget`
together with, for every `ω` avoiding it, deterministic refinements satisfying every `(k, p)`
postcondition at once — parents at the same scale sharing the translation slot `ω k`. -/
theorem exists_joint_refinement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E] :
    ∀ ε > (0 : ℝ),
    ∃ Cε C_dens : ℝ, 0 < Cε ∧ 0 < C_dens ∧
    ∀ {M : ℕ}, 1 ≤ M →
    ∀ (δ ρ r : Fin M → NNReal),
      (∀ k, 0 < (δ k : ℝ)) →
      (∀ k, (δ k : ℝ) < 1) →
      (∀ k, (δ k : ℝ) ≤ (ρ k : ℝ)) →
      (∀ k, (ρ k : ℝ) ≤ 1) →
      (∀ k, 0 < (r k : ℝ)) →
      (∀ k, (r k : ℝ) ≤ (ρ k : ℝ)) →
    ∀ {ι : Type u} {α : Fin M → Type u}
      (P : ∀ k : Fin M, Finset (α k))
      (s : ∀ k : Fin M, α k → Finset ι)
      (T : ∀ k : Fin M, ι → Tube (δ k) E)
      (Tρ : ∀ k : Fin M, α k → Tube (ρ k) E),
      (∀ k, ∀ p ∈ P k, (s k p).Nonempty) →
      (∀ k, ∀ p ∈ P k, (Tρ k p).carrier ⊆ Metric.closedBall (0 : E) 4) →
      (∀ k, ∀ p ∈ P k, ∀ i ∈ s k p,
        (T k i).carrier ⊆ (Tρ k p).carrier) →
    ∀ (M_dens : ∀ k : Fin M, α k → ℝ),
      (∀ k, ∀ p ∈ P k,
        (maxDensity (s k p) (fun i => (T k i).toConvexSpaceBody)).toReal ≤ M_dens k p) →
    ∀ (J : Fin M → ℕ), (∀ k, 1 ≤ J k) →
      (∀ k, ∀ p ∈ P k,
        (J k : ℝ) * ((s k p).card : ℝ) * probConst E (r k : ℝ) *
          ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
            (δ k : ℝ) ^ (Module.finrank ℝ E - 1)) < M_dens k p) →
    ∀ (ε_budget : ENNReal), 0 < ε_budget → ε_budget < 1 →
    ∀ (A : Fin M → ℝ),
      (∀ k, Cε * ((δ k : ℝ) ^ (-ε) +
        Real.log ((∑ l : Fin M, ((P l).card : ℝ)) / ε_budget.toReal)) ≤
          A k) →
    ∃ Bad : Set (∀ k : Fin M, Fin (J k) → E),
      MeasurableSet Bad ∧
      HasUniformTranslation.productMeasureIndexed E E J Bad ≤ ε_budget ∧
      (∀ ω : ∀ k : Fin M, Fin (J k) → E, ω ∉ Bad →
        ∃ s' : ∀ k : Fin M, α k → Finset (ι × Fin (J k)),
          ∀ k : Fin M, ∀ p ∈ P k,
            (∀ j, ‖(r k : ℝ) • ω k j‖ ≤ (r k : ℝ)) ∧
            s' k p ⊆ s k p ×ˢ Finset.univ ∧
            (A k)⁻¹ * (J k : ℝ) * ((s k p).card : ℝ) ≤
              ((s' k p).card : ℝ) ∧
            ((s' k p).card : ℝ) ≤ (J k : ℝ) * ((s k p).card : ℝ) ∧
            maxDensity (s' k p)
                (fun a =>
                  ((T k a.1).translate ((r k : ℝ) • ω k a.2)).toConvexSpaceBody) ≤
              ENNReal.ofReal (C_dens * A k * M_dens k p) ∧
            maxDensity (s k p ×ˢ Finset.univ)
                (fun a =>
                  ((T k a.1).translate ((r k : ℝ) • ω k a.2)).toConvexSpaceBody) ≤
              ENNReal.ofReal (C_dens * A k * M_dens k p)) := by
  classical
  intro ε hε
  obtain ⟨Cε, C_dens, hCε_pos, hC_dens_pos, h_scheme⟩ :=
    exists_refinement E ε hε
  refine ⟨Cε, C_dens, hCε_pos, hC_dens_pos, ?_⟩
  intro M hM δ ρ r hδ_pos hδ_lt_one hδ_le_ρ hρ_le_one hr_pos hr_le_ρ
    ι α P s T Tρ hs_ne hTρ_sub hT_sub_Tρ
    M_dens hM_dens_bound J hJ_ge_one hCalib ε_budget hε_budget_pos hε_budget_lt_one A
    h_calib1
  set N : ℕ := ∑ l : Fin M, (P l).card with hN_def
  by_cases hN_zero : N = 0
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp
    · intro ω _
      refine ⟨fun _ _ => ∅, ?_⟩
      intro k p hp
      exfalso
      have hPk_zero : (P k).card = 0 := by
        have : (P k).card ≤ N := by
          rw [hN_def]
          exact Finset.single_le_sum (f := fun l : Fin M => (P l).card)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega
      have : P k = ∅ := Finset.card_eq_zero.mp hPk_zero
      rw [this] at hp
      exact Finset.notMem_empty _ hp
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_zero
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_ne_zero_enn : (N : ENNReal) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; exact hN_zero
  have hN_ne_top_enn : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hε_budget_ne_top : ε_budget ≠ ⊤ := LT.lt.ne_top hε_budget_lt_one
  have hε_budget_ne_zero : ε_budget ≠ 0 := ne_of_gt hε_budget_pos
  have hε_budget_toReal_pos : 0 < ε_budget.toReal :=
    ENNReal.toReal_pos hε_budget_ne_zero hε_budget_ne_top
  set ε_per : ENNReal := ε_budget / N with hε_per_def
  have hε_per_pos : 0 < ε_per := by
    rw [hε_per_def]
    exact ENNReal.div_pos hε_budget_ne_zero hN_ne_top_enn
  have hε_per_le_budget : ε_per ≤ ε_budget := by
    rw [hε_per_def, ENNReal.div_le_iff' hN_ne_zero_enn hN_ne_top_enn]
    refine le_mul_of_one_le_left' ?_
    exact_mod_cast hN_pos
  have hε_per_lt_one : ε_per < 1 :=
    lt_of_le_of_lt hε_per_le_budget hε_budget_lt_one
  have hε_per_toReal : ε_per.toReal = ε_budget.toReal / N := by
    rw [hε_per_def, ENNReal.toReal_div]
    simp
  have h_log_eq : Real.log (1 / ε_per.toReal) =
      Real.log ((N : ℝ) / ε_budget.toReal) := by
    rw [hε_per_toReal]
    congr 1
    field_simp
  have hN_real_eq : (N : ℝ) = ∑ l : Fin M, ((P l).card : ℝ) := by
    rw [hN_def]
    push_cast
    rfl
  have h_calib1_per : ∀ k,
      Cε * ((δ k : ℝ) ^ (-ε) + Real.log (1 / ε_per.toReal)) ≤ A k := by
    intro k
    have hk := h_calib1 k
    rw [h_log_eq, hN_real_eq]
    exact hk
  set Bad : ∀ k : Fin M, ∀ p : α k, Set (Fin (J k) → E) := fun k p =>
    if h : p ∈ P k then
      Classical.choose (h_scheme (hδ_pos k) (hδ_lt_one k) (hδ_le_ρ k)
        (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
        (hs_ne k p h) (hTρ_sub k p h) (hT_sub_Tρ k p h)
        (M_dens k p) (hM_dens_bound k p h)
        (J k) (hJ_ge_one k) (hCalib k p h)
        ε_per hε_per_pos hε_per_lt_one (A k)
        (h_calib1_per k))
    else ∅ with hBad_def
  have hBad_spec : ∀ k : Fin M, ∀ p : α k, (hp : p ∈ P k) →
      Bad k p = Classical.choose (h_scheme (hδ_pos k) (hδ_lt_one k) (hδ_le_ρ k)
        (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
        (hs_ne k p hp) (hTρ_sub k p hp) (hT_sub_Tρ k p hp)
        (M_dens k p) (hM_dens_bound k p hp)
        (J k) (hJ_ge_one k) (hCalib k p hp)
        ε_per hε_per_pos hε_per_lt_one (A k)
        (h_calib1_per k)) := by
    intro k p hp; rw [hBad_def]; simp [hp]
  have hBad_meas : ∀ k : Fin M, ∀ p : α k, MeasurableSet (Bad k p) := by
    intro k p
    by_cases hp : p ∈ P k
    · rw [hBad_spec k p hp]
      exact (Classical.choose_spec (h_scheme (hδ_pos k) (hδ_lt_one k) (hδ_le_ρ k)
        (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
        (hs_ne k p hp) (hTρ_sub k p hp) (hT_sub_Tρ k p hp)
        (M_dens k p) (hM_dens_bound k p hp)
        (J k) (hJ_ge_one k) (hCalib k p hp)
        ε_per hε_per_pos hε_per_lt_one (A k)
        (h_calib1_per k))).1
    · have : Bad k p = ∅ := by rw [hBad_def]; simp [hp]
      rw [this]; exact MeasurableSet.empty
  have hBad_measure : ∀ k : Fin M, ∀ p : α k, p ∈ P k →
      HasUniformTranslation.productMeasure E E (J k) (Bad k p) ≤ ε_per := by
    intro k p hp
    rw [hBad_spec k p hp]
    exact (Classical.choose_spec (h_scheme (hδ_pos k) (hδ_lt_one k) (hδ_le_ρ k)
      (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
      (hs_ne k p hp) (hTρ_sub k p hp) (hT_sub_Tρ k p hp)
      (M_dens k p) (hM_dens_bound k p hp)
      (J k) (hJ_ge_one k) (hCalib k p hp)
      ε_per hε_per_pos hε_per_lt_one (A k)
      (h_calib1_per k))).2.1
  set BadScale : ∀ k : Fin M, Set (Fin (J k) → E) :=
    fun k => ⋃ p ∈ P k, Bad k p with hBadScale_def
  have hBadScale_meas : ∀ k : Fin M, MeasurableSet (BadScale k) := by
    intro k
    rw [hBadScale_def]
    refine Finset.measurableSet_biUnion _ ?_
    intro p _
    exact hBad_meas k p
  have hBadScale_measure : ∀ k : Fin M,
      HasUniformTranslation.productMeasure E E (J k) (BadScale k) ≤
        (P k).card * ε_per := by
    intro k
    rw [hBadScale_def]
    calc HasUniformTranslation.productMeasure E E (J k) (⋃ p ∈ P k, Bad k p)
        ≤ ∑ p ∈ P k, HasUniformTranslation.productMeasure E E (J k) (Bad k p) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ P k, ε_per :=
          Finset.sum_le_sum (fun p hp => hBad_measure k p hp)
      _ = (P k).card * ε_per := by
          rw [Finset.sum_const, nsmul_eq_mul]
  set BadJoint : Set (∀ k : Fin M, Fin (J k) → E) :=
    ⋃ k : Fin M, Function.eval k ⁻¹' BadScale k with hBadJoint_def
  have hBadJoint_meas : MeasurableSet BadJoint := by
    rw [hBadJoint_def]
    exact HasUniformTranslation.measurableSet_productMeasureIndexed_unionBad
      J BadScale hBadScale_meas
  have hBadJoint_measure :
      HasUniformTranslation.productMeasureIndexed E E J BadJoint ≤ ε_budget := by
    rw [hBadJoint_def]
    refine (HasUniformTranslation.productMeasureIndexed_union_bound (Ω := E) (E := E)
      J BadScale hBadScale_meas (fun k => (P k).card * ε_per)
      hBadScale_measure).trans ?_
    have hsum : ∑ k : Fin M, ((P k).card : ENNReal) * ε_per =
        (N : ENNReal) * ε_per := by
      rw [← Finset.sum_mul]
      congr 1
      rw [hN_def]
      push_cast
      rfl
    rw [hsum, hε_per_def]
    rw [ENNReal.mul_div_cancel hN_ne_zero_enn hN_ne_top_enn]
  refine ⟨BadJoint, hBadJoint_meas, hBadJoint_measure, ?_⟩
  intro ω hω_not
  have hω_per : ∀ k : Fin M, ∀ p ∈ P k, (ω k) ∉ Bad k p := by
    intro k p hp h_mem
    apply hω_not
    rw [hBadJoint_def]
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    change ω k ∈ BadScale k
    rw [hBadScale_def]
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hp, ?_⟩
    exact h_mem
  refine ⟨fun k p =>
    if h : p ∈ P k then
      Classical.choose ((by
        have hspec := (Classical.choose_spec (h_scheme (hδ_pos k)
          (hδ_lt_one k) (hδ_le_ρ k) (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
          (hs_ne k p h) (hTρ_sub k p h) (hT_sub_Tρ k p h)
          (M_dens k p) (hM_dens_bound k p h)
          (J k) (hJ_ge_one k) (hCalib k p h)
          ε_per hε_per_pos hε_per_lt_one (A k)
          (h_calib1_per k))).2.2
        have hω_k : ω k ∉ Classical.choose (h_scheme (hδ_pos k)
          (hδ_lt_one k) (hδ_le_ρ k) (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
          (hs_ne k p h) (hTρ_sub k p h) (hT_sub_Tρ k p h)
          (M_dens k p) (hM_dens_bound k p h)
          (J k) (hJ_ge_one k) (hCalib k p h)
          ε_per hε_per_pos hε_per_lt_one (A k)
          (h_calib1_per k)) := by
          have := hω_per k p h
          rwa [hBad_spec k p h] at this
        exact hspec (ω k) hω_k))
    else ∅, ?_⟩
  intro k p hp
  have h_spec := Classical.choose_spec (h_scheme (hδ_pos k)
    (hδ_lt_one k) (hδ_le_ρ k) (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
    (hs_ne k p hp) (hTρ_sub k p hp) (hT_sub_Tρ k p hp)
    (M_dens k p) (hM_dens_bound k p hp)
    (J k) (hJ_ge_one k) (hCalib k p hp)
    ε_per hε_per_pos hε_per_lt_one (A k)
    (h_calib1_per k))
  have hω_k : ω k ∉ Classical.choose (h_scheme (hδ_pos k)
    (hδ_lt_one k) (hδ_le_ρ k) (hρ_le_one k) (hr_pos k) (hr_le_ρ k) (s k p) (T k) (Tρ k p)
    (hs_ne k p hp) (hTρ_sub k p hp) (hT_sub_Tρ k p hp)
    (M_dens k p) (hM_dens_bound k p hp)
    (J k) (hJ_ge_one k) (hCalib k p hp)
    ε_per hε_per_pos hε_per_lt_one (A k)
    (h_calib1_per k)) := by
    have := hω_per k p hp
    rwa [hBad_spec k p hp] at this
  have h_inner := h_spec.2.2 (ω k) hω_k
  simp only [hp, dif_pos]
  exact Classical.choose_spec h_inner

end Kakeya.RandomTranslation
