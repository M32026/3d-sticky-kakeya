/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Probability
public import Kakeya.RandomTranslation.FrostmanCancellation

/-!
# Chernoff bound for the total ED bad count of `J` rigid copies

GWZ Lemma 3.8 applies `J` **independent** rigid motions and needs the total bad count
`∑_{j<J} X_j` against a fixed test tube to be small with high probability. The tail bound is GWZ
Lemma A.1, which this repository already has in fully general form as
`Kakeya.Probability.lemma_A1_case_lt`: for independent, identically distributed, `[0, M]`-valued
random variables with `J · 𝔼[X] < M`,

`P[∑_j X_j > S] ≤ exp (10e - S/M)`.

This file supplies the three hypotheses of that lemma for the rigid-motion bad counts:

* the sample space is the `J`-fold product `Kakeya.rigidPiMeasure`, so independence and identical
  distribution are structural (`iIndepFun_pi`, exactly as in
  `Kakeya.productTubeContainedCount_iIndepFun` for the translation-only case);
* the pointwise cap `X_j ≤ Cpack` is `Kakeya.edBadCount_le` — a *dimensional* constant, with no
  factor of `J`;
* the mean condition `J · 𝔼[X] < M` is the canonical Frostman cancellation
  `Kakeya.ceil_frostmanConstant_mul_lintegral_edBadCount_le`, with `J = ⌈C_F⌉₊`.

Because the cap and the mean bound are both dimensional, `M` can be chosen dimensional, and the
resulting threshold `S ≍ M · log(1/δ)` after a union bound over the `δ^(-O(1))` test-tube net is
`O(log(1/δ))` — independent of `C_F`. That is the whole point: it replaces the old
`M_ED := ⌈CF⌉₊ * C_pack_ext + 1`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The `J`-fold product of the rigid-motion probability space: `J` independent rigid motions. -/
def rigidPiMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (J : ℕ) :
    Measure (Fin J → (unitary (E →L[ℝ] E) × E)) :=
  Measure.pi fun _ => rigidMeasure E

instance instIsProbabilityMeasureRigidPiMeasure (J : ℕ) :
    IsProbabilityMeasure (rigidPiMeasure E J) := by
  unfold rigidPiMeasure
  infer_instance

/-- The bad count is a measurable function of the rigid motion. -/
theorem measurable_edBadCount {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) :
    Measurable (fun ω : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ ω : ℝ)) := by
  classical
  let P : (unitary (E →L[ℝ] E) × E) → ι → Prop := fun ω i =>
    ((T i).rigidMove ω.1 ω.2).carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀.carrier
  have hmeas : ∀ i ∈ s,
      Measurable (fun ω : unitary (E →L[ℝ] E) × E => if P ω i then (1 : ℝ) else 0) := by
    intro i hi
    have hPmeas : MeasurableSet {ω : (unitary (E →L[ℝ] E)) × E | P ω i} := by
      let K : ConvexSpaceBody E := T₀.toConvexSpaceBody.cthickening (99 * (δ : ℝ))
      have hcl : IsClosed {ω : (unitary (E →L[ℝ] E)) × E | P ω i} := by
        simpa [P, K, ConvexSpaceBody.cthickening] using isClosed_rigidMove_subset (T i) K
      exact hcl.measurableSet
    exact Measurable.ite hPmeas measurable_const measurable_const
  have h_eq : (fun ω : (unitary (E →L[ℝ] E)) × E => (edBadCount s T T₀ ω : ℝ))
      = fun ω => s.sum (fun i => if P ω i then (1 : ℝ) else 0) := by
    funext ω
    unfold edBadCount P
    exact (Finset.sum_boole (fun i => P ω i) s).symm
  rw [h_eq]
  exact Finset.measurable_fun_sum s hmeas

/-- The bad count of the `j`-th of `J` independent rigid copies. -/
def edBadCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E)
    (J : ℕ) (j : Fin J) (ω : Fin J → (unitary (E →L[ℝ] E) × E)) : ℝ :=
  (edBadCount s T T₀ (ω j) : ℝ)

theorem measurable_edBadCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) (j : Fin J) :
    Measurable (edBadCountAt s T T₀ J j) :=
  (measurable_edBadCount s T T₀).comp (measurable_pi_apply j)

/-- The bad counts of the `J` independent copies are jointly independent. -/
theorem iIndepFun_edBadCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) :
    ProbabilityTheory.iIndepFun (fun j => edBadCountAt s T T₀ J j) (rigidPiMeasure E J) := by
  unfold rigidPiMeasure edBadCountAt
  exact ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin J => rigidMeasure E)
    (X := fun _ : Fin J => fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ))
    (fun _ => (measurable_edBadCount s T T₀).aemeasurable)

/-- The bad counts of the `J` independent copies are identically distributed. -/
theorem identDistrib_edBadCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) (J : ℕ) (j₁ j₂ : Fin J) :
    ProbabilityTheory.IdentDistrib (edBadCountAt s T T₀ J j₁) (edBadCountAt s T T₀ J j₂)
      (rigidPiMeasure E J) (rigidPiMeasure E J) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ)) :=
    measurable_edBadCount s T T₀
  have hmap_eval : ∀ j : Fin J, (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    intro j
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  refine ⟨(measurable_edBadCountAt s T T₀ J j₁).aemeasurable,
          (measurable_edBadCountAt s T T₀ J j₂).aemeasurable, ?_⟩
  rw [show edBadCountAt s T T₀ J j₁ =
        (fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ)) ∘ Function.eval j₁ by rfl]
  rw [show edBadCountAt s T T₀ J j₂ =
        (fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ)) ∘ Function.eval j₂ by rfl]
  rw [← Measure.map_map hg (measurable_pi_apply j₁)]
  rw [← Measure.map_map hg (measurable_pi_apply j₂)]
  rw [hmap_eval j₁, hmap_eval j₂]

/-- The mean of one coordinate is the mean over a single rigid motion. -/
theorem integral_edBadCountAt {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (T₀ : Tube δ E) {J : ℕ} (j : Fin J) :
    ∫ ω, edBadCountAt s T T₀ J j ω ∂(rigidPiMeasure E J)
      = ∫ y, (edBadCount s T T₀ y : ℝ) ∂(rigidMeasure E) := by
  have hg : Measurable (fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ)) :=
    measurable_edBadCount s T T₀
  have hmap_eval : (rigidPiMeasure E J).map (Function.eval j) = rigidMeasure E := by
    rw [rigidPiMeasure]
    exact (measurePreserving_eval (μ := fun _ : Fin J => rigidMeasure E) j).map_eq
  have hmap_int :
    ∫ y, (edBadCount s T T₀ y : ℝ)
        ∂((rigidPiMeasure E J).map (Function.eval j))
      = ∫ ω, (edBadCount s T T₀ (Function.eval j ω) : ℝ)
          ∂(rigidPiMeasure E J) := by
    exact MeasureTheory.integral_map (measurable_pi_apply j).aemeasurable
      hg.aestronglyMeasurable
  change ∫ ω, (edBadCount s T T₀ (Function.eval j ω) : ℝ) ∂(rigidPiMeasure E J)
      = ∫ y, (edBadCount s T T₀ y : ℝ) ∂(rigidMeasure E)
  rw [← hmap_int]
  rw [hmap_eval]

/-- **The Chernoff tail bound for the total ED bad count of `J` independent rigid copies.**

The threshold constant `M` is *dimensional*: it depends only on `E`, not on `δ`, not on the family,
and above all not on the Frostman constant. That is exactly what fails for the old deterministic
`J`-fold union bound `M_ED := ⌈CF⌉₊ * C_pack_ext + 1`.

`J` is allowed to be any positive integer up to `⌈C_F⌉₊`; the intended instantiation is
`J = ⌈C_F⌉₊`, the number of random copies GWZ take. The mean hypothesis of GWZ Lemma A.1 is
supplied by the canonical Frostman cancellation. -/
theorem edBadCount_chernoff_tail [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (M : ℝ) (δ₀ : NNReal), 0 < M ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        ∀ (J : ℕ), 0 < J →
          (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
        ∀ (S : ℝ),
          ((rigidPiMeasure E J)
              {ω | ∑ j : Fin J, edBadCountAt s T T₀ J j ω > S}).toReal
            ≤ Real.exp (10 * Real.exp 1 - S / M) := by
  classical
  obtain ⟨Cpack, δ₁, hCpack_pos, hδ₁, hCap⟩ := edBadCount_le (E := E) hn
  obtain ⟨CED, δ₂, hCED_ne_top, hδ₂, hCanc⟩ :=
    ceil_frostmanConstant_mul_lintegral_edBadCount_le (E := E) hn
  let M : ℝ := CED.toReal + (Cpack : ℝ) + 1
  have hCED_nonneg : 0 ≤ CED.toReal := by exact ENNReal.toReal_nonneg (a := CED)
  have hCpack_nonneg : 0 ≤ (Cpack : ℝ) := by exact_mod_cast (Nat.zero_le Cpack)
  have hM_pos : 0 < M := by
    dsimp [M]
    nlinarith [hCED_nonneg, hCpack_nonneg]
  refine ⟨M, min δ₁ δ₂, hM_pos, lt_min hδ₁ hδ₂, ?_⟩
  intro δ hδ hδle ι s T T₀ hSub hED hB J hJ hJle S
  have hδle₁ : δ ≤ δ₁ := le_trans hδle (min_le_left δ₁ δ₂)
  have hδle₂ : δ ≤ δ₂ := le_trans hδle (min_le_right δ₁ δ₂)
  haveI : NeZero J := ⟨hJ.ne'⟩
  have hCpm : (Cpack : ℝ) ≤ M := by
    dsimp [M]
    nlinarith [hCED_nonneg, hCpack_nonneg]
  set m : ℝ := ∫ y, (edBadCount s T T₀ y : ℝ) ∂(rigidMeasure E) with hm_def
  set X : Fin J → (Fin J → (unitary (E →L[ℝ] E) × E)) → ℝ :=
      fun j ω => edBadCountAt s T T₀ J j ω with hX
  have hmeas : ∀ j : Fin J, Measurable (X j) := fun j => by
    simpa [X] using measurable_edBadCountAt s T T₀ J j
  have hnonneg : ∀ (j : Fin J) ω, 0 ≤ X j ω := by
    intro j ω
    dsimp [X]
    exact Nat.cast_nonneg _
  have hup : ∀ (j : Fin J) ω, X j ω ≤ M := by
    intro j ω
    have hcard : edBadCount s T T₀ (ω j) ≤ Cpack := hCap hδ hδle₁ s T T₀ hB hED (ω j)
    have hcardR : (edBadCount s T T₀ (ω j) : ℝ) ≤ (Cpack : ℝ) := by exact_mod_cast hcard
    have heq : X j ω = (edBadCount s T T₀ (ω j) : ℝ) := rfl
    rw [heq]
    exact le_trans hcardR hCpm
  have hbound : ∀ j : Fin J, ∀ᵐ ω ∂(rigidPiMeasure E J),
      0 ≤ X j ω ∧ X j ω ≤ M := fun j => by
    exact Filter.Eventually.of_forall fun ω => ⟨hnonneg j ω, hup j ω⟩
  have hmean : ∫ ω, X 0 ω ∂(rigidPiMeasure E J) = m := by
    rw [hX, hm_def]
    exact integral_edBadCountAt s T T₀ (0 : Fin J)
  have hindep : ProbabilityTheory.iIndepFun X (rigidPiMeasure E J) := by
    simpa [X] using iIndepFun_edBadCountAt s T T₀ J
  have hid : ∀ j : Fin J,
      ProbabilityTheory.IdentDistrib (X j) (X 0) (rigidPiMeasure E J)
        (rigidPiMeasure E J) := fun j => by
    simpa [X] using identDistrib_edBadCountAt s T T₀ J j 0
  let I : ENNReal := ∫⁻ x, (edBadCount s T T₀ x : ENNReal) ∂(rigidMeasure E)
  let CF : ENNReal := ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
  let CFn : ℕ := ⌈CF.toReal⌉₊
  have hJle2 : (J : ℝ) ≤ (CFn : ℝ) := by
    simpa [CFn] using hJle
  have hcanc1 : (CFn : ENNReal) * I ≤ CED := by
    simpa [CFn] using hCanc hδ hδle₂ s T T₀ hSub hED
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact MeasureTheory.integral_nonneg fun Z => Nat.cast_nonneg _
  have hint_ae : 0 ≤ᵐ[rigidMeasure E] (fun r : unitary (E →L[ℝ] E) × E =>
      (edBadCount s T T₀ r : ℝ)) :=
    Filter.Eventually.of_forall fun r => Nat.cast_nonneg _
  have hint_int : Integrable (fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ))
      (rigidMeasure E) := by
    refine MeasureTheory.Integrable.of_bound
      (f := fun y : unitary (E →L[ℝ] E) × E => (edBadCount s T T₀ y : ℝ)) ?_ (Cpack : ℝ) ?_
    · exact (measurable_edBadCount s T T₀).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        have hv : edBadCount s T T₀ y ≤ Cpack := hCap hδ hδle₁ s T T₀ hB hED y
        have hvR : (edBadCount s T T₀ y : ℝ) ≤ (Cpack : ℝ) := by exact_mod_cast hv
        have hnn0 : 0 ≤ (edBadCount s T T₀ y : ℝ) := Nat.cast_nonneg _
        simpa [abs_of_nonneg hnn0] using hvR
  have hbridge : ENNReal.ofReal m = I := by
    calc
      ENNReal.ofReal m
          = ∫⁻ y, ENNReal.ofReal ((edBadCount s T T₀ y : ℝ)) ∂(rigidMeasure E) := by
              rw [hm_def]
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_int hint_ae
      _ = I := by
              dsimp [I]
              apply lintegral_congr
              intro y
              rw [ENNReal.ofReal_natCast]
  have hof : ENNReal.ofReal ((CFn : ℝ) * m) ≤ CED := by
    calc
      ENNReal.ofReal ((CFn : ℝ) * m)
          = ENNReal.ofReal (CFn : ℝ) * ENNReal.ofReal m := by
              rw [ENNReal.ofReal_mul (by exact_mod_cast (Nat.zero_le CFn))]
      _ = (CFn : ENNReal) * ENNReal.ofReal m := by rw [ENNReal.ofReal_natCast]
      _ = (CFn : ENNReal) * I := by rw [hbridge]
      _ ≤ CED := hcanc1
  have h_real : (CFn : ℝ) * m ≤ CED.toReal := by
    have hmono := ENNReal.toReal_mono hCED_ne_top hof
    rw [ENNReal.toReal_ofReal (mul_nonneg (by exact_mod_cast (Nat.zero_le CFn)) hm_nonneg)] at hmono
    exact hmono
  have hJle_mul : (J : ℝ) * m ≤ (CFn : ℝ) * m :=
    (mul_le_mul_of_nonneg_right hJle2 hm_nonneg)
  have hJm : (J : ℝ) * m < M := by
    have hCedR : CED.toReal < M := by
      dsimp [M]
      nlinarith [hCpack_nonneg]
    nlinarith [hJle_mul, h_real, hCedR]
  have hmM : m ≤ M := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne J))
    have hle_m : m ≤ (J : ℝ) * m := by
      have htmp := mul_le_mul_of_nonneg_right h1 hm_nonneg
      simpa using htmp
    linarith [hJm, hle_m]
  simpa [X, M] using
    Probability.lemma_A1_case_lt (P := rigidPiMeasure E J) (N := J) (X := X)
      hmeas M hM_pos m hm_nonneg hmM hbound hmean hindep hid S hJm

end

end Kakeya

end
