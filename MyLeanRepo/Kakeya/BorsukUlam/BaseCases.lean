/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.Degree.Homology

open TopCat Metric

/-!
# Base Cases and Reduction for Borsuk-Ulam
-/

namespace BorsukUlam

/-- The antipodal map on `𝕊 n`. -/
def sphereAntipodal (n : ℕ) (x : 𝕊 n) : 𝕊 n :=
  ULift.up ⟨-x.down.1, by simp⟩

/-- A canonical point on the sphere. -/
def spherePoint (n : ℕ) : 𝕊 n :=
  let f : Fin (n + 1) → ℝ := fun i => if i = 0 then 1 else 0
  let v : EuclideanSpace ℝ (Fin (n + 1)) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm f
  ULift.up ⟨v, by
    have h_norm : ‖v‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      have h_sum : ∑ i : Fin (n + 1), ‖v i‖ ^ 2 = 1 := by
        have h_vals : ∀ i : Fin (n + 1), v i = f i := by intro i; rfl
        simp [h_vals, f, Finset.sum_ite, Finset.filter_eq'] <;> norm_num
      rw [h_sum] <;> norm_num
    exact mem_sphere_zero_iff_norm.mpr h_norm⟩

instance (n : ℕ) : Nonempty (𝕊 n) := ⟨spherePoint n⟩

/-- Append a zero coordinate to a function on `Fin k`. -/
def appendZero (k : ℕ) (v : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0

/-- `appendZero` is continuous. -/
theorem continuous_appendZero (k : ℕ) : Continuous (appendZero k) := by
  apply continuous_pi
  intro i
  by_cases h : i.val < k
  · have h' : (fun v : Fin k → ℝ => appendZero k v i) = fun v => v ⟨i.val, h⟩ := by
      funext v
      simp [appendZero, h]
    rw [h']
    exact continuous_apply _
  · have h' : (fun v : Fin k → ℝ => appendZero k v i) = fun _ => (0 : ℝ) := by
      funext v
      simp [appendZero, h] <;> omega
    rw [h']
    exact continuous_const

/-- Extend a Euclidean vector by appending a zero coordinate. -/
noncomputable def extendZero (k : ℕ) (v : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin (k + 1)) :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm
    (appendZero k ((PiLp.continuousLinearEquiv 2 ℝ _) v))

/-- `extendZero` is continuous. -/
theorem continuous_extendZero (k : ℕ) : Continuous (extendZero k) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp
    ((continuous_appendZero k).comp (PiLp.continuousLinearEquiv 2 ℝ _).continuous)

/-- The components of `extendZero k v`. -/
theorem extendZero_apply (k : ℕ) (v : EuclideanSpace ℝ (Fin k)) (i : Fin (k + 1)) :
    (extendZero k v) i = if h : i.val < k then v ⟨i.val, h⟩ else 0 := by
  simp [extendZero, appendZero, PiLp.continuousLinearEquiv, WithLp.equiv_symm_apply]
  <;> rfl

/-- `extendZero` preserves the norm. -/
theorem norm_extendZero (k : ℕ) (v : EuclideanSpace ℝ (Fin k)) :
    ‖extendZero k v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have h_sum : ∑ i : Fin (k + 1), ‖(extendZero k v) i‖ ^ 2 =
      ∑ i : Fin k, ‖v i‖ ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    have h_last : ‖(extendZero k v) (Fin.last k)‖ ^ 2 = 0 := by
      rw [extendZero_apply]
      have h : ¬(Fin.last k).val < k := by
        simp [Fin.last]
        <;> exact Nat.lt_irrefl k
      simp [h] <;> norm_num
    have h_cast : ∑ i : Fin k, ‖(extendZero k v) (Fin.castSucc i)‖ ^ 2 =
        ∑ i : Fin k, ‖v i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [extendZero_apply]
      have h : (Fin.castSucc i).val < k := by
        exact Fin.is_lt i
      simp [h]
    rw [h_cast, h_last, add_zero]
  exact h_sum

/-- The equatorial embedding `𝕊 n → 𝕊 (n + 1)`. -/
noncomputable def equatorialEmbedding (n : ℕ) : 𝕊 n → 𝕊 (n + 1) :=
  fun x =>
    let v : EuclideanSpace ℝ (Fin (n + 1)) := x.down.val
    let w : EuclideanSpace ℝ (Fin (n + 2)) := extendZero (n + 1) v
    have hw : ‖w‖ = 1 := by
      rw [norm_extendZero]
      exact mem_sphere_zero_iff_norm.mp x.down.property
    ULift.up ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩

/-- The equatorial embedding is continuous. -/
theorem continuous_equatorialEmbedding (n : ℕ) :
    Continuous (equatorialEmbedding n) := by
  have h_down : Continuous (fun x : 𝕊 n => (x.down : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val.comp continuous_uliftDown
  have h_ext : Continuous (fun x : 𝕊 n => extendZero (n + 1) (x.down : EuclideanSpace ℝ (Fin (n + 1)))) :=
    (continuous_extendZero (n + 1)).comp h_down
  have h_sphere : Continuous (fun x : 𝕊 n =>
      (⟨extendZero (n + 1) (x.down : EuclideanSpace ℝ (Fin (n + 1))),
        mem_sphere_zero_iff_norm.mpr (by
          rw [norm_extendZero]
          exact mem_sphere_zero_iff_norm.mp x.down.property)⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) := by
    exact Continuous.subtype_mk h_ext fun x =>
      mem_sphere_zero_iff_norm.mpr (by
        rw [norm_extendZero]
        exact mem_sphere_zero_iff_norm.mp x.down.property)
  exact continuous_uliftUp.comp h_sphere

/-- The equatorial embedding commutes with the antipodal map. -/
theorem equatorialEmbedding_antipodal (n : ℕ) (x : 𝕊 n) :
    equatorialEmbedding n (sphereAntipodal n x) =
    sphereAntipodal (n + 1) (equatorialEmbedding n x) := by
  apply ULift.ext
  apply Subtype.ext
  ext i
  simp [equatorialEmbedding, sphereAntipodal, extendZero_apply]
  <;> split_ifs <;> simp_all <;> ring_nf <;> omega

/-- Base case `j = 0`. -/
theorem borsuk_ulam_j_zero (n : ℕ) (f : 𝕊 n → EuclideanSpace ℝ (Fin 0))
    (_hf_cont : Continuous f) (_hf_odd : ∀ x, f (sphereAntipodal n x) = -f x) :
    0 ∈ Set.range f := by
  have h : ∀ (y : EuclideanSpace ℝ (Fin 0)), y = 0 := by
    intro y
    exact Subsingleton.elim y 0
  let x : 𝕊 n := Classical.arbitrary (𝕊 n)
  refine ⟨x, ?_⟩
  exact h (f x)

/-- `𝕊 1` is path-connected. -/
theorem pathConnected_sphere1 : PathConnectedSpace (𝕊 1) := by
  have h1 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
    have h3 : Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) = ↑(Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := by
      exact Eq.symm (Module.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin 2)))
    rw [h3, h2] <;> norm_num
  have h3 : IsPathConnected (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_sphere h1 0 (by norm_num)
  have h4 : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp h3
  exact ULift.up_surjective.pathConnectedSpace continuous_uliftUp

/-- Base case `n = 1, j = 1`. -/
theorem borsuk_ulam_n1_j1 (f : 𝕊 1 → ℝ)
    (hf_cont : Continuous f) (hf_odd : ∀ x, f (sphereAntipodal 1 x) = -f x) :
    0 ∈ Set.range f := by
  letI : PathConnectedSpace (𝕊 1) := pathConnected_sphere1
  let x : 𝕊 1 := spherePoint 1
  by_cases h : f x = 0
  · exact ⟨x, h⟩
  · have h_odd : f (sphereAntipodal 1 x) = -f x := hf_odd x
    let γ : Path x (sphereAntipodal 1 x) :=
      PathConnectedSpace.somePath x (sphereAntipodal 1 x)
    let g : ℝ → ℝ := fun t => f (γ.extend t)
    have hg_cont : Continuous g := hf_cont.comp γ.continuous_extend
    have h0 : g 0 = f x := by simp [g]
    have h1 : g 1 = f (sphereAntipodal 1 x) := by simp [g]
    by_cases hpos : 0 < f x
    · have h_ivt : ∃ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 := by
        apply intermediate_value_Icc' (by norm_num) hg_cont.continuousOn
        rw [h0, h1, h_odd]
        <;> exact ⟨by linarith, by linarith⟩
      rcases h_ivt with ⟨t, _, ht⟩
      exact ⟨γ.extend t, ht⟩
    · have hneg : f x < 0 := by
        have h5 : ¬0 < f x := hpos
        have h6 : f x ≠ 0 := h
        by_contra h7
        have h8 : 0 ≤ f x := by linarith
        have h9 : f x = 0 := by linarith
        exact h6 h9
      have h_ivt : ∃ t ∈ Set.Icc (0 : ℝ) 1, g t = 0 := by
        apply intermediate_value_Icc (by norm_num) hg_cont.continuousOn
        rw [h0, h1, h_odd]
        <;> exact ⟨by linarith, by linarith⟩
      rcases h_ivt with ⟨t, _, ht⟩
      exact ⟨γ.extend t, ht⟩

/-- Reduction from `j < n` to the inductive hypothesis.
    Given Borsuk-Ulam for `(n, j)`, prove it for `(n + 1, j)` when `j ≤ n`. -/
theorem borsuk_ulam_reduction {n j : ℕ} (hjn : j ≤ n)
    (f : 𝕊 (n + 1) → EuclideanSpace ℝ (Fin j))
    (hf_cont : Continuous f)
    (hf_odd : ∀ x, f (sphereAntipodal (n + 1) x) = -f x)
    (h_ind : ∀ (g : 𝕊 n → EuclideanSpace ℝ (Fin j)),
      Continuous g → (∀ x, g (sphereAntipodal n x) = -g x) → 0 ∈ Set.range g) :
    0 ∈ Set.range f := by
  let i : 𝕊 n → 𝕊 (n + 1) := equatorialEmbedding n
  let g : 𝕊 n → EuclideanSpace ℝ (Fin j) := f ∘ i
  have hg_cont : Continuous g := hf_cont.comp (continuous_equatorialEmbedding n)
  have hg_odd : ∀ x, g (sphereAntipodal n x) = -g x := by
    intro x
    calc
      g (sphereAntipodal n x)
        = f (i (sphereAntipodal n x)) := rfl
      _ = f (sphereAntipodal (n + 1) (i x)) := by
        have h_eq : i (sphereAntipodal n x) = sphereAntipodal (n + 1) (i x) :=
          equatorialEmbedding_antipodal n x
        rw [h_eq]
      _ = -f (i x) := hf_odd (i x)
      _ = -g x := rfl
  have h_main : 0 ∈ Set.range g := h_ind g hg_cont hg_odd
  rcases h_main with ⟨y, hy⟩
  exact ⟨i y, hy⟩

end BorsukUlam
