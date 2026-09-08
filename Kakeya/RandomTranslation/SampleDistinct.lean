/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.TranslationProb
public import Mathlib

/-!
# Almost-sure distinctness of the sampled translation vectors

The random-translation construction of GWZ Lemma 7.5 draws, at each scale `k`,
a family `(ω k j)_{j < J k}` of translation vectors and then uses the *number*
of distinct translates as a lower bound on the size of the translation set
`R k`.  For that count to be `J k` rather than merely `≤ J k`, the sampled
vectors must be pairwise distinct.

They are, almost surely: the sampling measure `uniformBallMeasure` is a scalar
multiple of `volume.restrict (closedBall 0 1)`, hence has no atoms, so the
collision event `{ω | ω j = ω j'}` is null for `j ≠ j'`.  A finite union over
the scales and the pairs of slots is then null as well, and can be added to the
random-translation `Bad` set at no cost to the measure budget.

This file supplies exactly that: atomlessness of the sampling measure, and the
nullity (with measurability) of the collision event on the single-scale product
space `Fin J → E` and on the joint space `∀ k, Fin (J k) → E`.  The same
budget-free exclusion is provided for the escape event `‖ω k j‖ > 1`, since the
sampling measure is supported on the closed unit ball.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory
open Set

namespace Kakeya.RandomTranslation

section Atomless

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The uniform measure on the unit ball has no atoms: it is a scalar multiple of a
restriction of `volume`, which is an additive Haar measure on a nontrivial
finite-dimensional real inner product space. -/
instance instNullSingletonClassUniformBallMeasure :
    NoAtoms (uniformBallMeasure E) := by
  refine ⟨fun x => ?_⟩
  change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
      volume.restrict (Metric.closedBall (0 : E) 1)) {x} = 0
  rw [Measure.smul_apply, measure_singleton, smul_zero]

end Atomless

section Collision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
/-- The single-scale collision event is measurable. -/
lemma measurableSet_collision (J : ℕ) (j j' : Fin J) :
    MeasurableSet {ω : Fin J → E | ω j = ω j'} := by
  apply measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply j')

/-- **Two distinct sampling slots almost surely disagree.**  The joint law of the
pair `(ω j, ω j')` under the product measure is `μ.prod μ` with `μ` atomless, and
the diagonal is `μ.prod μ`-null. -/
lemma productMeasure_collision_null (J : ℕ) {j j' : Fin J} (hjj' : j ≠ j') :
    HasUniformTranslation.productMeasure E E J {ω : Fin J → E | ω j = ω j'} = 0 := by
  set μ := HasUniformTranslation.measure (Ω := E) (E := E) with hμ_def
  set P := HasUniformTranslation.productMeasure E E J with hP_def
  have h_collision_eq : {ω : Fin J → E | ω j = ω j'} =
      (fun ω : Fin J → E => (ω j, ω j'))⁻¹' (Set.diagonal E) := by
    ext ω; simp [Set.diagonal]
  rw [h_collision_eq]
  have h_map_prod : P.map (fun ω : Fin J → E => (ω j, ω j')) = μ.prod μ := by
    have h_indep : ProbabilityTheory.IndepFun (fun ω : Fin J → E => ω j)
        (fun ω : Fin J → E => ω j') P := by
      have hiIndep : ProbabilityTheory.iIndepFun (fun (i : Fin J) (ω : Fin J → E) => ω i) P := by
        have hmeas : ∀ i : Fin J, AEMeasurable (id : E → E) μ :=
          fun i => (measurable_id (α := E)).aemeasurable
        have := iIndepFun_pi (μ := fun _ : Fin J => μ) (X := fun _ : Fin J => (id : E → E)) hmeas
        simpa [P, HasUniformTranslation.productMeasure, hμ_def] using this
      exact hiIndep.indepFun hjj'
    have hmeas_j : AEMeasurable (fun ω : Fin J → E => ω j) P :=
      (measurable_pi_apply j).aemeasurable
    have hmeas_j' : AEMeasurable (fun ω : Fin J → E => ω j') P :=
      (measurable_pi_apply j').aemeasurable
    have h_eq : P.map (fun ω : Fin J → E => ω j) = μ := by
      have h := HasUniformTranslation.productMeasure_map_eval (Ω := E) (E := E) J j
      simpa [P, hμ_def.symm] using h
    have h_eq' : P.map (fun ω : Fin J → E => ω j') = μ := by
      have h := HasUniformTranslation.productMeasure_map_eval (Ω := E) (E := E) J j'
      simpa [P, hμ_def.symm] using h
    have h_iff := (indepFun_iff_map_prod_eq_prod_map_map hmeas_j hmeas_j').mp h_indep
    simpa [h_eq, h_eq'] using h_iff
  have h_meas_pair : Measurable (fun ω : Fin J → E => (ω j, ω j')) :=
    (measurable_pi_apply j).prodMk (measurable_pi_apply j')
  rw [← Measure.map_apply h_meas_pair measurableSet_diagonal, h_map_prod]
  have hμ_singleton : ∀ x : E, μ {x} = 0 := by
    intro x
    have hμ_eq : μ = uniformBallMeasure E := by
      calc
        μ = HasUniformTranslation.measure (Ω := E) (E := E) := hμ_def
        _ = (instHasUniformTranslationSelf (E := E)).measure := rfl
        _ = uniformBallMeasure E := rfl
    rw [hμ_eq]
    exact measure_singleton (μ := uniformBallMeasure E) x
  have h_diagonal_null : (μ.prod μ) (Set.diagonal E) = 0 := by
    refine Measure.measure_prod_null_of_ae_null (measurableSet_diagonal (α := E)) ?_
    have h_slice : ∀ x : E, Prod.mk x ⁻¹' Set.diagonal E = {x} := by
      intro x; ext y; simp [Set.diagonal, eq_comm]
    have h_ae : (fun x : E => μ (Prod.mk x ⁻¹' Set.diagonal E)) =ᵐ[μ] 0 := by
      filter_upwards [] with x
      simp [h_slice x, hμ_singleton x]
    exact h_ae
  exact h_diagonal_null

/-- The joint (all-scales) collision event. -/
def jointCollision {M : ℕ} (J : Fin M → ℕ) : Set (∀ k : Fin M, Fin (J k) → E) :=
  {ω | ∃ k : Fin M, ∃ j j' : Fin (J k), j ≠ j' ∧ ω k j = ω k j'}

/-- **The sampled translation vectors are almost surely pairwise distinct at every
scale.**  A finite union of null single-scale collision events. -/
lemma productMeasureIndexed_jointCollision_null {M : ℕ} (J : Fin M → ℕ) :
    HasUniformTranslation.productMeasureIndexed E E J (jointCollision (E := E) J) = 0 := by
  set μ := HasUniformTranslation.productMeasureIndexed E E J with hμ_def
  have h_sub : jointCollision (E := E) J ⊆
    ⋃ (k : Fin M), (Function.eval k)⁻¹' (⋃ (j : Fin (J k)) (j' : Fin (J k)) (_ : j ≠ j'),
      {ω : Fin (J k) → E | ω j = ω j'}) := by
    intro ω hω
    rcases hω with ⟨k, j, j', hne, h⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    have hmem : (ω k) ∈ ⋃ (j : Fin (J k)) (j' : Fin (J k)) (_ : j ≠ j'),
        {ω : Fin (J k) → E | ω j = ω j'} := by
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine Set.mem_iUnion.mpr ⟨j', ?_⟩
      refine Set.mem_iUnion.mpr ⟨hne, ?_⟩
      simp [h]
    simpa [Function.eval] using hmem
  have h_union_zero : μ (⋃ (k : Fin M), (Function.eval k)⁻¹'
      (⋃ (j : Fin (J k)) (j' : Fin (J k)) (_ : j ≠ j'),
        {ω : Fin (J k) → E | ω j = ω j'})) = 0 := by
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro k
    have h_meas_union : MeasurableSet (⋃ (j : Fin (J k)) (j' : Fin (J k)) (_ : j ≠ j'),
      {ω : Fin (J k) → E | ω j = ω j'}) := by
      refine MeasurableSet.iUnion (fun j => ?_)
      refine MeasurableSet.iUnion (fun j' => ?_)
      refine MeasurableSet.iUnion (fun (hne : j ≠ j') => ?_)
      exact measurableSet_collision (J k) j j'
    rw [HasUniformTranslation.productMeasureIndexed_preimage_eval
      (Ω := E) (E := E) J k h_meas_union]
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro j
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro j'
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro hne
    exact productMeasure_collision_null (J k) hne
  have h_le : μ (jointCollision (E := E) J) ≤ 0 := by
    calc
      μ (jointCollision (E := E) J) ≤ μ (⋃ (k : Fin M), (Function.eval k)⁻¹'
      (⋃ (j : Fin (J k)) (j' : Fin (J k)) (_ : j ≠ j'),
        {ω : Fin (J k) → E | ω j = ω j'})) := measure_mono h_sub
      _ = 0 := h_union_zero
  have h_nonneg : 0 ≤ μ (jointCollision (E := E) J) := by simp
  exact le_antisymm h_le h_nonneg

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- Off the joint collision event, each scale's sampling map is injective. -/
lemma injective_of_notMem_jointCollision {M : ℕ} {J : Fin M → ℕ}
    {ω : ∀ k : Fin M, Fin (J k) → E} (hω : ω ∉ jointCollision (E := E) J) (k : Fin M) :
    Function.Injective (ω k) := by
  intro x y hxy
  by_contra hne
  apply hω
  refine Set.mem_setOf.mpr ?_
  exact ⟨k, x, y, hne, hxy⟩

end Collision

section PiSlice

/-- **Slice criterion for nullity under a finite product measure.**  If, for every choice `g` of the
coordinates other than `i₀`, the `i₀`-slice of a measurable set `S` is null for `μ i₀`, then `S`
itself is null for `Measure.pi μ`. -/
lemma measure_pi_eq_zero_of_slice_eq_zero {m : ℕ} {α : Fin (m + 1) → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (i₀ : Fin (m + 1))
    {S : Set (∀ i, α i)} (hS : MeasurableSet S)
    (h : ∀ g : ∀ j : Fin m, α (i₀.succAbove j),
      μ i₀ {x : α i₀ | i₀.insertNth x g ∈ S} = 0) :
    Measure.pi μ S = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove α i₀
  have h_mp : MeasurePreserving e (Measure.pi μ)
      ((μ i₀).prod (Measure.pi fun j => μ (i₀.succAbove j))) :=
    measurePreserving_piFinSuccAbove μ i₀
  set ν := Measure.pi fun j : Fin m => μ (i₀.succAbove j) with hν_def
  have hT_meas : MeasurableSet (e.symm⁻¹' S) :=
    (MeasurableEquiv.symm e).measurable hS
  have hS_eq : S = e⁻¹' (e.symm⁻¹' S) :=
    (MeasurableEquiv.symm_preimage_preimage (e.symm) S).symm
  have h_eq : Measure.pi μ S = ((μ i₀).prod ν) (e.symm⁻¹' S) := by
    calc
      Measure.pi μ S = Measure.pi μ (e⁻¹' (e.symm⁻¹' S)) :=
        congrArg (Measure.pi μ) hS_eq
      _ = (Measure.map e (Measure.pi μ)) (e.symm⁻¹' S) := by
        rw [Measure.map_apply h_mp.measurable hT_meas]
      _ = ((μ i₀).prod ν) (e.symm⁻¹' S) := by rw [h_mp.map_eq]
  rw [h_eq]
  have h_swap : MeasurePreserving Prod.swap ((μ i₀).prod ν) (ν.prod (μ i₀)) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hU_meas : MeasurableSet (Prod.swap⁻¹' (e.symm⁻¹' S)) :=
    measurable_swap hT_meas
  have h_swap_eq : ((μ i₀).prod ν) (e.symm⁻¹' S) =
      (ν.prod (μ i₀)) (Prod.swap⁻¹' (e.symm⁻¹' S)) := by
    have h_inv : Prod.swap⁻¹' (Prod.swap⁻¹' (e.symm⁻¹' S)) = e.symm⁻¹' S := by
      simp [Set.preimage, Prod.swap]
    calc
      ((μ i₀).prod ν) (e.symm⁻¹' S) = ((μ i₀).prod ν)
          (Prod.swap⁻¹' (Prod.swap⁻¹' (e.symm⁻¹' S))) := by
        rw [h_inv]
      _ = (Measure.map Prod.swap ((μ i₀).prod ν)) (Prod.swap⁻¹' (e.symm⁻¹' S)) := by
        rw [Measure.map_apply measurable_swap hU_meas]
      _ = (ν.prod (μ i₀)) (Prod.swap⁻¹' (e.symm⁻¹' S)) := by rw [h_swap.map_eq]
  rw [h_swap_eq]
  have h_slice : (fun g : ∀ j : Fin m, α (i₀.succAbove j) =>
      (μ i₀) (Prod.mk g ⁻¹' (Prod.swap⁻¹' (e.symm⁻¹' S)))) =ᵐ[ν] 0 := by
    have h_slice_eq : ∀ g, Prod.mk g ⁻¹' (Prod.swap⁻¹' (e.symm⁻¹' S)) =
        {x : α i₀ | i₀.insertNth x g ∈ S} := by
      intro g; ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Prod.swap_prod_mk]
      have hx_eq : e.symm (x, g) = i₀.insertNth x g :=
        calc
          e.symm (x, g) = (Fin.insertNthEquiv α i₀) (x, g) := by
            simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply α i₀]
          _ = i₀.insertNth x g := rfl
      rw [hx_eq]
    have h_zero : ∀ g, (μ i₀) (Prod.mk g ⁻¹' (Prod.swap⁻¹' (e.symm⁻¹' S))) = 0 := by
      intro g; rw [h_slice_eq g]; exact h g
    filter_upwards [] with g; exact h_zero g
  exact Measure.measure_prod_null_of_ae_null hU_meas h_slice

end PiSlice

section SumCollision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **Two distinct sampling slots almost surely do not differ by a prescribed vector.**
The joint law of the pair `(ω j, ω j')` is `μ.prod μ` with `μ` atomless, and each slice of
`{(a, b) | a - b = z}` is a singleton. -/
lemma productMeasure_shiftCollision_null (J : ℕ) {j j' : Fin J} (hjj' : j ≠ j') (z : E) :
    HasUniformTranslation.productMeasure E E J {ω : Fin J → E | ω j - ω j' = z} = 0 := by
  set μ := HasUniformTranslation.measure (Ω := E) (E := E) with hμ_def
  set P := HasUniformTranslation.productMeasure E E J with hP_def
  set Dz := {p : E × E | p.1 - p.2 = z} with hDz_def
  have h_collision_eq : {ω : Fin J → E | ω j - ω j' = z} =
      (fun ω : Fin J → E => (ω j, ω j'))⁻¹' Dz := by
    ext ω; simp [hDz_def]
  rw [h_collision_eq]
  have h_map_prod : P.map (fun ω : Fin J → E => (ω j, ω j')) = μ.prod μ := by
    have h_indep : ProbabilityTheory.IndepFun (fun ω : Fin J → E => ω j)
        (fun ω : Fin J → E => ω j') P := by
      have hiIndep : ProbabilityTheory.iIndepFun (fun (i : Fin J) (ω : Fin J → E) => ω i) P := by
        have hmeas : ∀ i : Fin J, AEMeasurable (id : E → E) μ :=
          fun i => (measurable_id (α := E)).aemeasurable
        have := iIndepFun_pi (μ := fun _ : Fin J => μ) (X := fun _ : Fin J => (id : E → E)) hmeas
        simpa [P, HasUniformTranslation.productMeasure, hμ_def] using this
      exact hiIndep.indepFun hjj'
    have hmeas_j : AEMeasurable (fun ω : Fin J → E => ω j) P :=
      (measurable_pi_apply j).aemeasurable
    have hmeas_j' : AEMeasurable (fun ω : Fin J → E => ω j') P :=
      (measurable_pi_apply j').aemeasurable
    have h_eq : P.map (fun ω : Fin J → E => ω j) = μ := by
      have h := HasUniformTranslation.productMeasure_map_eval (Ω := E) (E := E) J j
      simpa [P, hμ_def.symm] using h
    have h_eq' : P.map (fun ω : Fin J → E => ω j') = μ := by
      have h := HasUniformTranslation.productMeasure_map_eval (Ω := E) (E := E) J j'
      simpa [P, hμ_def.symm] using h
    have h_iff := (indepFun_iff_map_prod_eq_prod_map_map hmeas_j hmeas_j').mp h_indep
    simpa [h_eq, h_eq'] using h_iff
  have h_meas_Dz : MeasurableSet Dz := by
    dsimp [Dz]
    apply measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const
  have h_meas_pair : Measurable (fun ω : Fin J → E => (ω j, ω j')) :=
    (measurable_pi_apply j).prodMk (measurable_pi_apply j')
  rw [← Measure.map_apply h_meas_pair h_meas_Dz, h_map_prod]
  have hμ_singleton : ∀ x : E, μ {x} = 0 := by
    intro x
    have hμ_eq : μ = uniformBallMeasure E := by
      calc
        μ = HasUniformTranslation.measure (Ω := E) (E := E) := hμ_def
        _ = (instHasUniformTranslationSelf (E := E)).measure := rfl
        _ = uniformBallMeasure E := rfl
    rw [hμ_eq]
    exact measure_singleton (μ := uniformBallMeasure E) x
  have h_Dz_null : (μ.prod μ) Dz = 0 := by
    refine Measure.measure_prod_null_of_ae_null h_meas_Dz ?_
    have h_slice : ∀ x : E, Prod.mk x ⁻¹' Dz = {x - z} := by
      intro x; ext y
      simp only [hDz_def, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h
        calc
          y = (x - (x - y)) := by abel
          _ = x - z := by rw [h]
      · intro h
        calc
          x - y = x - (x - z) := by rw [h]
          _ = z := by abel
    have h_ae : (fun x : E => μ (Prod.mk x ⁻¹' Dz)) =ᵐ[μ] 0 := by
      filter_upwards [] with x
      rw [h_slice x]
      exact hμ_singleton (x - z)
    exact h_ae
  exact h_Dz_null

/-- The joint event that two *distinct* paths through the per-scale sampling slots produce
the same weighted sum of sampled vectors.  Excluding it makes the total prefix offset
determine the path, which is the multiplicity clause of GWZ Lemma 7.6 in its sharpest
possible form (multiplicity exactly one). -/
def jointSumCollision {M : ℕ} (J : Fin M → ℕ) (c : Fin M → ℝ) :
    Set (∀ k : Fin M, Fin (J k) → E) :=
  {ω | ∃ j j' : ∀ k : Fin M, Fin (J k), j ≠ j' ∧
      ∑ k, c k • ω k (j k) = ∑ k, c k • ω k (j' k)}

/-- **Distinct paths almost surely produce distinct weighted sums.**  Fix a pair of
distinct paths and a scale `k₀` where they differ; conditioning on all other coordinates
turns the collision into a shifted single-scale collision, which is null. -/
lemma productMeasureIndexed_jointSumCollision_null {M : ℕ} (J : Fin M → ℕ) (c : Fin M → ℝ)
    (hc : ∀ k, c k ≠ 0) :
    HasUniformTranslation.productMeasureIndexed E E J (jointSumCollision (E := E) J c) = 0 := by
  classical
    obtain _ | m := M
    · have h_empty : jointSumCollision (E := E) J c = ∅ := by
        ext ω; simp [jointSumCollision]
      simp [h_empty]
    · rename_i m
      set μ := HasUniformTranslation.productMeasureIndexed E E J with hμ_def
      let A (j j' : ∀ k : Fin (m + 1), Fin (J k)) : Set (∀ k : Fin (m + 1), Fin (J k) → E) :=
        {ω | ∑ k, c k • ω k (j k) = ∑ k, c k • ω k (j' k)}
      have h_sub : jointSumCollision (E := E) J c ⊆
          ⋃ (j : ∀ k : Fin (m + 1), Fin (J k))
            (j' : ∀ k : Fin (m + 1), Fin (J k)) (_ : j ≠ j'), A j j' := by
        intro ω hω
        rcases hω with ⟨j, j', hne, h⟩
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        refine Set.mem_iUnion.mpr ⟨j', ?_⟩
        refine Set.mem_iUnion.mpr ⟨hne, ?_⟩
        exact h
      have h_fintype : Fintype (∀ k : Fin (m + 1), Fin (J k)) := by
        infer_instance
      have h_union_zero : μ (⋃ (j : ∀ k : Fin (m + 1), Fin (J k))
          (j' : ∀ k : Fin (m + 1), Fin (J k)) (_ : j ≠ j'), A j j') = 0 := by
        rw [MeasureTheory.measure_iUnion_null_iff]
        intro j
        rw [MeasureTheory.measure_iUnion_null_iff]
        intro j'
        rw [MeasureTheory.measure_iUnion_null_iff]
        intro hne
        have h_exists : ∃ k₀ : Fin (m + 1), j k₀ ≠ j' k₀ := by
          by_contra! h
          exact hne (funext h)
        rcases h_exists with ⟨k₀, hjk⟩
        have hmeas_A : MeasurableSet (A j j') := by
          have hmeas_eval (j : ∀ k : Fin (m + 1), Fin (J k)) :
            Measurable (fun ω : ∀ k : Fin (m + 1), Fin (J k) → E => ∑ k, c k • ω k (j k)) := by
            refine Finset.measurable_sum (Finset.univ : Finset (Fin (m + 1))) ?_
            intro k hk
            have hmeas_comp : Measurable (fun ω : ∀ k : Fin (m + 1), Fin (J k) → E => ω k (j k)) :=
              (measurable_pi_apply (j k)).comp (measurable_pi_apply k)
            have hmeas_smul : Measurable (fun (x : E) => c k • x) :=
              (measurable_const_smul (c k))
            exact hmeas_smul.comp hmeas_comp
          exact measurableSet_eq_fun (hmeas_eval j) (hmeas_eval j')
        set μ' := fun (k : Fin (m + 1)) =>
          HasUniformTranslation.productMeasure E E (J k) with hμ'_def
        have hμ'_sigma : ∀ k : Fin (m + 1), SigmaFinite (μ' k) := by
          intro k; infer_instance
        have hμ_eq' : μ = Measure.pi μ' := rfl
        rw [hμ_eq']
        apply measure_pi_eq_zero_of_slice_eq_zero (m := m)
          (α := fun k : Fin (m + 1) => Fin (J k) → E)
          μ' k₀ hmeas_A
        intro g
        let α : Fin (m + 1) → Type _ := fun k : Fin (m + 1) => Fin (J k) → E
        set Aconst := ∑ l : Fin m, c (k₀.succAbove l) • g l (j (k₀.succAbove l)) with hAconst_def
        set Bconst := ∑ l : Fin m, c (k₀.succAbove l) • g l (j' (k₀.succAbove l)) with hBconst_def
        set z := (c k₀)⁻¹ • (Bconst - Aconst) with hz_def
        have h_slice_eq : {θ : Fin (J k₀) → E | (k₀.insertNth (α := α) θ g) ∈ A j j'} =
            {θ : Fin (J k₀) → E | θ (j k₀) - θ (j' k₀) = z} := by
          ext θ; constructor
          · intro hθ
            have hθ_in_eq : ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) := by
              have htemp1 : (k₀.insertNth (α := α) θ g) ∈ A j j' := Set.mem_setOf.mp hθ
              exact Set.mem_setOf.mp htemp1
            have hsum_l : ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                c k₀ • θ (j k₀) + Aconst := by
              calc
                ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                    (c k₀ • ((k₀.insertNth (α := α) θ g) k₀) (j k₀)) +
                    ∑ l : Fin m, c (k₀.succAbove l) •
                      ((k₀.insertNth (α := α) θ g) (k₀.succAbove l)) (j (k₀.succAbove l)) := by
                  rw [Fin.sum_univ_succAbove
                    (fun k => c k • ((k₀.insertNth (α := α) θ g) k) (j k)) k₀]
                _ = c k₀ • θ (j k₀) +
                  ∑ l : Fin m, c (k₀.succAbove l) • g l (j (k₀.succAbove l)) := by
                  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
                _ = c k₀ • θ (j k₀) + Aconst := rfl
            have hsum_r : ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) =
                c k₀ • θ (j' k₀) + Bconst := by
              calc
                ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) =
                    (c k₀ • ((k₀.insertNth (α := α) θ g) k₀) (j' k₀)) +
                    ∑ l : Fin m, c (k₀.succAbove l) •
                      ((k₀.insertNth (α := α) θ g) (k₀.succAbove l)) (j' (k₀.succAbove l)) := by
                  rw [Fin.sum_univ_succAbove
                    (fun k => c k • ((k₀.insertNth (α := α) θ g) k) (j' k)) k₀]
                _ = c k₀ • θ (j' k₀) +
                  ∑ l : Fin m, c (k₀.succAbove l) • g l (j' (k₀.succAbove l)) := by
                  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
                _ = c k₀ • θ (j' k₀) + Bconst := rfl
            have h_eq_sums : c k₀ • θ (j k₀) + Aconst = c k₀ • θ (j' k₀) + Bconst := by
              calc
                c k₀ • θ (j k₀) + Aconst = ∑ k : Fin (m + 1), c k •
                  ((k₀.insertNth (α := α) θ g) k) (j k) := by
                  symm; exact hsum_l
                _ = ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) := hθ_in_eq
                _ = c k₀ • θ (j' k₀) + Bconst := hsum_r
            have h_eq_sub : c k₀ • (θ (j k₀) - θ (j' k₀)) = Bconst - Aconst := by
              calc
                c k₀ • (θ (j k₀) - θ (j' k₀)) =
                  (c k₀ • θ (j k₀)) - (c k₀ • θ (j' k₀)) := by rw [smul_sub]
                _ = (c k₀ • θ (j k₀) + Aconst) - (c k₀ • θ (j' k₀) + Aconst) := by abel
                _ = (c k₀ • θ (j' k₀) + Bconst) - (c k₀ • θ (j' k₀) + Aconst) := by rw [h_eq_sums]
                _ = Bconst - Aconst := by abel
            have h_inv_smul : θ (j k₀) - θ (j' k₀) = (c k₀)⁻¹ • (Bconst - Aconst) := by
              calc
                θ (j k₀) - θ (j' k₀) = (1 : ℝ) • (θ (j k₀) - θ (j' k₀)) := by simp
                _ = ((c k₀)⁻¹ * c k₀) • (θ (j k₀) - θ (j' k₀)) := by
                  rw [inv_mul_cancel₀ (hc k₀)]
                _ = (c k₀)⁻¹ • (c k₀ • (θ (j k₀) - θ (j' k₀))) := by simp [smul_smul]
                _ = (c k₀)⁻¹ • (Bconst - Aconst) := by rw [h_eq_sub]
                _ = z := rfl
            exact h_inv_smul
          · intro hθ
            have hθ_eq : θ (j k₀) - θ (j' k₀) = z := hθ
            have hsum_l : ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                c k₀ • θ (j k₀) + Aconst := by
              calc
                ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                    (c k₀ • ((k₀.insertNth (α := α) θ g) k₀) (j k₀)) +
                    ∑ l : Fin m, c (k₀.succAbove l) •
                      ((k₀.insertNth (α := α) θ g) (k₀.succAbove l)) (j (k₀.succAbove l)) := by
                  rw [Fin.sum_univ_succAbove
                    (fun k => c k • ((k₀.insertNth (α := α) θ g) k) (j k)) k₀]
                _ = c k₀ • θ (j k₀) +
                  ∑ l : Fin m, c (k₀.succAbove l) • g l (j (k₀.succAbove l)) := by
                  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
                _ = c k₀ • θ (j k₀) + Aconst := rfl
            have hsum_r : ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) =
                c k₀ • θ (j' k₀) + Bconst := by
              calc
                ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) =
                    (c k₀ • ((k₀.insertNth (α := α) θ g) k₀) (j' k₀)) +
                    ∑ l : Fin m, c (k₀.succAbove l) •
                      ((k₀.insertNth (α := α) θ g) (k₀.succAbove l)) (j' (k₀.succAbove l)) := by
                  rw [Fin.sum_univ_succAbove
                    (fun k => c k • ((k₀.insertNth (α := α) θ g) k) (j' k)) k₀]
                _ = c k₀ • θ (j' k₀) +
                  ∑ l : Fin m, c (k₀.succAbove l) • g l (j' (k₀.succAbove l)) := by
                  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
                _ = c k₀ • θ (j' k₀) + Bconst := rfl
            have htemp : c k₀ • (θ (j k₀) - θ (j' k₀)) = Bconst - Aconst := by
              calc
                c k₀ • (θ (j k₀) - θ (j' k₀)) = c k₀ • z := by rw [hθ_eq]
                _ = c k₀ • ((c k₀)⁻¹ • (Bconst - Aconst)) := rfl
                _ = (c k₀ * (c k₀)⁻¹) • (Bconst - Aconst) := by simp [smul_smul]
                _ = 1 • (Bconst - Aconst) := by simp [hc k₀]
                _ = Bconst - Aconst := by simp
            have h_eq_sums : c k₀ • θ (j k₀) + Aconst = c k₀ • θ (j' k₀) + Bconst := by
              calc
                c k₀ • θ (j k₀) + Aconst =
                  (c k₀ • θ (j k₀) - c k₀ • θ (j' k₀)) +
                  (c k₀ • θ (j' k₀) + Aconst) := by abel
                _ = (c k₀ • (θ (j k₀) - θ (j' k₀))) +
                  (c k₀ • θ (j' k₀) + Aconst) := by rw [smul_sub]
                _ = (Bconst - Aconst) + (c k₀ • θ (j' k₀) + Aconst) := by rw [htemp]
                _ = c k₀ • θ (j' k₀) + Bconst := by abel
            calc
              ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j k) =
                c k₀ • θ (j k₀) + Aconst := hsum_l
              _ = c k₀ • θ (j' k₀) + Bconst := h_eq_sums
              _ = ∑ k : Fin (m + 1), c k • ((k₀.insertNth (α := α) θ g) k) (j' k) := hsum_r.symm
        rw [h_slice_eq]
        exact productMeasure_shiftCollision_null (J k₀) hjk z
      have h_le : μ (jointSumCollision (E := E) J c) ≤ 0 := by
        calc
          μ (jointSumCollision (E := E) J c) ≤ μ (⋃ (j : ∀ k : Fin (m + 1), Fin (J k))
            (j' : ∀ k : Fin (m + 1), Fin (J k)) (_ : j ≠ j'), A j j') :=
            measure_mono h_sub
          _ = 0 := h_union_zero
      have h_nonneg : 0 ≤ μ (jointSumCollision (E := E) J c) := by simp
      exact le_antisymm h_le h_nonneg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- Off the joint sum-collision event, the weighted-sum map on paths is injective. -/
lemma sum_injective_of_notMem_jointSumCollision {M : ℕ} {J : Fin M → ℕ} {c : Fin M → ℝ}
    {ω : ∀ k : Fin M, Fin (J k) → E} (hω : ω ∉ jointSumCollision (E := E) J c) :
    Function.Injective (fun j : ∀ k : Fin M, Fin (J k) => ∑ k, c k • ω k (j k)) := by
  intro j j' hjj'
  by_contra hne
  exact hω ⟨j, j', hne, hjj'⟩

end SumCollision

section Outside

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The joint event that some sampled vector escapes the unit ball.  The sampling measure is
supported on the closed unit ball, so this is null; excluding it makes the norm bound
`‖ω k j‖ ≤ 1` available at *every* scale, including scales whose parent family is empty. -/
def jointOutside {M : ℕ} (J : Fin M → ℕ) : Set (∀ k : Fin M, Fin (J k) → E) :=
  {ω | ∃ k : Fin M, ∃ j : Fin (J k), ω k j ∉ Metric.closedBall (0 : E) 1}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The single-scale escape event is measurable. -/
lemma measurableSet_outside (J : ℕ) :
    MeasurableSet {ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} := by
  have h_eq : {ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} =
    ⋃ (j : Fin J), (Function.eval j)⁻¹' ((Metric.closedBall (0 : E) 1)ᶜ) := by
    ext ω; simp [Function.eval]
  rw [h_eq]
  refine MeasurableSet.iUnion (fun j => ?_)
  have h_meas_eval : Measurable (Function.eval j : (Fin J → E) → E) :=
    measurable_pi_apply j
  have h_meas_ball : MeasurableSet ((Metric.closedBall (0 : E) 1)ᶜ) :=
    (Metric.isClosed_closedBall (α := E)).measurableSet.compl
  exact h_meas_eval h_meas_ball

/-- **Almost surely every sampled vector at a single scale lies in the unit ball.**  Under the
canonical product uniform-translation measure each coordinate is distributed according to
`uniformBallMeasure E`, which is concentrated on the closed unit ball, so each
`{ω | ω j ∉ closedBall 0 1}` is null and the union across `Fin J` is null as well. -/
lemma productMeasure_outside_null (J : ℕ) [NeZero J] :
    HasUniformTranslation.productMeasure E E J
        {ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} = 0 := by
  set μ : MeasureTheory.Measure (Fin J → E) :=
    HasUniformTranslation.productMeasure E E J with hμ_def
  haveI : MeasureTheory.IsProbabilityMeasure μ :=
    HasUniformTranslation.productMeasure_isProbabilityMeasure E E J
  have hOutside_eq :
      {ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} =
        ⋃ j : Fin J, {ω : Fin J → E | ω j ∉ Metric.closedBall (0 : E) 1} := by
    ext ω; simp
  have hBall_meas : MeasurableSet (Metric.closedBall (0 : E) 1) :=
    Metric.isClosed_closedBall.measurableSet
  have hCompl_meas : MeasurableSet ((Metric.closedBall (0 : E) 1)ᶜ) :=
    hBall_meas.compl
  have hcoord_zero : ∀ j : Fin J,
      μ {ω : Fin J → E | ω j ∉ Metric.closedBall (0 : E) 1} = 0 := by
    intro j
    have hpre :
        {ω : Fin J → E | ω j ∉ Metric.closedBall (0 : E) 1} =
          (Function.eval j : (Fin J → E) → E) ⁻¹'
            ((Metric.closedBall (0 : E) 1)ᶜ) := by
      ext ω; simp [Function.eval]
    rw [hpre]
    have hmeas_eval : Measurable (Function.eval j : (Fin J → E) → E) :=
      measurable_pi_apply j
    have hmap_apply :
        μ ((Function.eval j : (Fin J → E) → E) ⁻¹'
            ((Metric.closedBall (0 : E) 1)ᶜ)) =
          (uniformBallMeasure E) ((Metric.closedBall (0 : E) 1)ᶜ) := by
      rw [← MeasureTheory.Measure.map_apply hmeas_eval hCompl_meas]
      rw [show μ = HasUniformTranslation.productMeasure E E J from hμ_def]
      rw [HasUniformTranslation.productMeasure_map_eval]
      rfl
    rw [hmap_apply]
    change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
          MeasureTheory.Measure.restrict volume (Metric.closedBall (0 : E) 1))
            ((Metric.closedBall (0 : E) 1)ᶜ) = 0
    rw [MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.restrict_apply hCompl_meas]
    simp
  rw [hOutside_eq]
  refine MeasureTheory.measure_iUnion_null_iff.mpr ?_
  intro j; exact hcoord_zero j

/-- **Almost surely every sampled vector lies in the unit ball.** -/
lemma productMeasureIndexed_jointOutside_null {M : ℕ} (J : Fin M → ℕ) (hJ : ∀ k, 0 < J k) :
    HasUniformTranslation.productMeasureIndexed E E J (jointOutside (E := E) J) = 0 := by
  set μ := HasUniformTranslation.productMeasureIndexed E E J with hμ_def
  have h_sub : jointOutside (E := E) J ⊆
    ⋃ (k : Fin M), (Function.eval k)⁻¹'
      {ω : Fin (J k) → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} := by
    intro ω hω
    rcases hω with ⟨k, j, hj⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    have hmem : (ω k) ∈ {ω : Fin (J k) → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} := by
      refine Set.mem_setOf.mpr ?_
      exact ⟨j, hj⟩
    simpa [Function.eval] using hmem
  have h_union_zero : μ (⋃ (k : Fin M), (Function.eval k)⁻¹'
      {ω : Fin (J k) → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1}) = 0 := by
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro k
    have h_meas_outside : MeasurableSet
        {ω : Fin (J k) → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1} :=
      measurableSet_outside (J k)
    rw [HasUniformTranslation.productMeasureIndexed_preimage_eval
      (Ω := E) (E := E) J k h_meas_outside]
    haveI : NeZero (J k) := ⟨(hJ k).ne'⟩
    exact productMeasure_outside_null (E := E) (J k)
  have h_le : μ (jointOutside (E := E) J) ≤ 0 := by
    calc
      μ (jointOutside (E := E) J) ≤ μ (⋃ (k : Fin M), (Function.eval k)⁻¹'
        {ω : Fin (J k) → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1}) :=
        measure_mono h_sub
      _ = 0 := h_union_zero
  have h_nonneg : 0 ≤ μ (jointOutside (E := E) J) := by simp
  exact le_antisymm h_le h_nonneg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Off the joint escape event, every sampled vector has norm at most one. -/
lemma norm_le_one_of_notMem_jointOutside {M : ℕ} {J : Fin M → ℕ}
    {ω : ∀ k : Fin M, Fin (J k) → E} (hω : ω ∉ jointOutside (E := E) J)
    (k : Fin M) (j : Fin (J k)) : ‖ω k j‖ ≤ 1 := by
  by_contra! h
  apply hω
  refine Set.mem_setOf.mpr ?_
  refine ⟨k, j, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact not_le.mpr h

end Outside

end Kakeya.RandomTranslation

end
