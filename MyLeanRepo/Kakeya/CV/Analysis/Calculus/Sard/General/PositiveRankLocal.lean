/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.LocalStraightening
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.RankFormulaFubini
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma rank_lower_semicontinuous {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (r : ℕ) :
    IsOpen {L : V →L[ℝ] W | r < Module.finrank ℝ (LinearMap.range L.toLinearMap)} := by
  have h_exists_lin_indep (p : Submodule ℝ W) (k : ℕ) (hk : k ≤ Module.finrank ℝ p) :
      ∃ (w : Fin k → p), LinearIndependent ℝ w := by
    let n := Module.finrank ℝ p
    have hkn : k ≤ n := hk
    let b : Basis (Fin n) ℝ p := by
      exact finBasis ℝ p
    let w : Fin k → p := fun i : Fin k => b (Fin.castLE hkn i)
    have hw_lin : LinearIndependent ℝ w := b.linearIndependent.comp _ (Fin.castLE_injective hkn)
    exact ⟨w, hw_lin⟩
  have h_main : ∀ (L0 : V →L[ℝ] W), L0 ∈ {L : V →L[ℝ] W | r < Module.finrank ℝ (LinearMap.range L.toLinearMap)} →
      ∃ (t : Set (V →L[ℝ] W)), t ⊆ {L : V →L[ℝ] W | r < Module.finrank ℝ (LinearMap.range L.toLinearMap)} ∧
        IsOpen t ∧ L0 ∈ t := by
    intro L0 hL0
    let r' := r + 1
    have h1 : r' ≤ Module.finrank ℝ (LinearMap.range L0.toLinearMap) := hL0
    set p : Submodule ℝ W := LinearMap.range L0.toLinearMap with hp
    have h_exists_w : ∃ (w : Fin r' → p), LinearIndependent ℝ w := h_exists_lin_indep p r' h1
    rcases h_exists_w with ⟨w, hw_lin⟩
    have h_forall : ∀ (i : Fin r'), ∃ (vi : V), L0.toLinearMap vi = (w i : W) := by
      intro i
      have h6 : (w i : W) ∈ p := (w i).property
      exact LinearMap.mem_range.mp h6
    choose v hv using h_forall
    let F : (V →L[ℝ] W) → (Fin r' → W) := fun L => fun i : Fin r' => L (v i)
    have hF_cont : Continuous F := by fun_prop
    let U₀ : Set (Fin r' → W) := {g | LinearIndependent ℝ g}
    have hU₀_open : IsOpen U₀ := isOpen_setOf_linearIndependent
    let U : Set (V →L[ℝ] W) := F ⁻¹' U₀
    have hU_open : IsOpen U := hU₀_open.preimage hF_cont
    let f : p →ₗ[ℝ] W := Submodule.subtype p
    have hf_ker : LinearMap.ker f = ⊥ := by
      simp [f, Submodule.ker_subtype]
    let w' : Fin r' → W := f ∘ w
    have h_w'_lin : LinearIndependent ℝ w' := hw_lin.map' f hf_ker
    have hL0_in_U : L0 ∈ U := by
      have h_eq : (F L0) = w' := by
        funext i
        exact (hv i)
      rw [show U = F ⁻¹' U₀ from rfl]
      rw [Set.mem_preimage, h_eq]
      exact h_w'_lin
    have h4 : U ⊆ {L : V →L[ℝ] W | r < Module.finrank ℝ (LinearMap.range L.toLinearMap)} := by
      intro L hL
      have h5 : LinearIndependent ℝ (F L) := by simpa [U, U₀] using hL
      have h6 : ∀ (i : Fin r'), (F L) i ∈ LinearMap.range L.toLinearMap := by
        intro i
        exact LinearMap.mem_range_self _ _
      let pL : Submodule ℝ W := LinearMap.range L.toLinearMap
      let fL : Fin r' → pL := fun i => ⟨(F L) i, h6 i⟩
      let f2 : pL →ₗ[ℝ] W := Submodule.subtype pL
      have h_eq2 : f2 ∘ fL = F L := by
        funext i
        rfl
      have h5' : LinearIndependent ℝ (f2 ∘ fL) := by
        have h : (f2 ∘ fL) = (F L) := h_eq2
        rw [h]
        exact h5
      have h_fL_lin : LinearIndependent ℝ fL := LinearIndependent.of_comp f2 h5'
      have h7 : Fintype.card (Fin r') ≤ Module.finrank ℝ pL :=
        LinearIndependent.fintype_card_le_finrank h_fL_lin
      have h8 : Fintype.card (Fin r') = r' := by simp [r']
      rw [h8] at h7
      have h9 : r < r' := by simp [r']
      have h10 : r < Module.finrank ℝ pL := lt_of_lt_of_le h9 h7
      exact h10
    exact ⟨U, h4, hU_open, hL0_in_U⟩
  exact isOpen_iff_forall_mem_open.mpr h_main

lemma helper_slice_is_critical {m n r : ℕ} (hnm : n < m) (hr : r ≤ n) (s : ℕ) (h : s < n - r) :
    s < m - r ∧ s < n - r := by
  have h1 : s < n - r := h
  have h2 : n - r ≤ m - r := by omega
  have h3 : s < m - r := by linarith
  exact ⟨h3, h1⟩

lemma helper_rank_fun_measurable {m n r : ℕ} (G : (E r × E (m - r)) → E (n - r))
    (hG : ContDiff ℝ ∞ G) (k : ℕ) :
    MeasurableSet {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < k} := by
  let φ : (E r × E (m - r)) → (E (m - r) →L[ℝ] E (n - r)) := fun z =>
    ((fderiv ℝ G z).toLinearMap.comp (LinearMap.inr ℝ (E r) (E (m - r)))).toContinuousLinearMap
  have h_cont_fderiv : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  let inr_clm : (E (m - r)) →L[ℝ] (E r × E (m - r)) :=
    (LinearMap.inr ℝ (E r) (E (m - r))).toContinuousLinearMap
  let C : ( (E r × E (m - r) →L[ℝ] E (n - r)) ) → (E (m - r) →L[ℝ] E (n - r)) := fun L =>
    L.comp inr_clm
  have hC_bounded : IsBoundedLinearMap ℝ C :=
    ContinuousLinearMap.isBoundedLinearMap_comp_right (f := inr_clm)
  have hC_cont : Continuous C := hC_bounded.continuous
  have h1 : Continuous φ := by
    have h : φ = C ∘ (fderiv ℝ G) := by
      funext z
      rfl
    rw [h]
    exact hC_cont.comp h_cont_fderiv
  have h2 : ∀ (z : E r × E (m - r)), fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 =
      Module.finrank ℝ (LinearMap.range (φ z).toLinearMap) := by
    intro z
    have h_eq1 : (fderiv ℝ (fun b : E (m - r) => G (z.1, b)) z.2).toLinearMap = (φ z).toLinearMap := by
      exact our_partial_deriv G hG z
    rw [fderivRank, h_eq1]
  cases k with
  | zero =>
    have h_empty : {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < 0} = (∅ : Set (E r × E (m - r))) := by
      ext z
      simp
    rw [h_empty]
    exact MeasurableSet.empty
  | succ k' =>
    have h3 : IsOpen {L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      rank_lower_semicontinuous k'
    have h4 : MeasurableSet {L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      h3.measurableSet
    have h5 : {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < k'.succ} =
        φ ⁻¹' ({L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)})ᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_compl_iff, Nat.lt_succ_iff]
      let a := Module.finrank ℝ (LinearMap.range (φ z).toLinearMap)
      have h_iff1 : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 ≤ k' ↔ a ≤ k' := by
        have h_eq2 : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 = a := h2 z
        exact h_eq2 ▸ Iff.rfl
      have h_iff2 : a ≤ k' ↔ ¬ (k' < a) := by
        exact Iff.symm Nat.not_lt
      have h_final : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 ≤ k' ↔ ¬ (k' < a) := by
        rw [h_iff1, h_iff2]
      exact h_final
    rw [h5]
    exact h4.compl.preimage h1.measurable

lemma helper_Smeas_closed {m n r : ℕ} (G : (E r × E (m - r)) → E (n - r))
    (hG : ContDiff ℝ ∞ G) (k : ℕ) :
    IsClosed {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < k} := by
  let φ : (E r × E (m - r)) → (E (m - r) →L[ℝ] E (n - r)) := fun z =>
    ((fderiv ℝ G z).toLinearMap.comp (LinearMap.inr ℝ (E r) (E (m - r)))).toContinuousLinearMap
  have h_cont_fderiv : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  let inr_clm : (E (m - r)) →L[ℝ] (E r × E (m - r)) :=
    (LinearMap.inr ℝ (E r) (E (m - r))).toContinuousLinearMap
  let C : ( (E r × E (m - r) →L[ℝ] E (n - r)) ) → (E (m - r) →L[ℝ] E (n - r)) := fun L =>
    L.comp inr_clm
  have hC_bounded : IsBoundedLinearMap ℝ C :=
    ContinuousLinearMap.isBoundedLinearMap_comp_right (f := inr_clm)
  have hC_cont : Continuous C := hC_bounded.continuous
  have hφ_cont : Continuous φ := by
    have h : φ = C ∘ (fderiv ℝ G) := by
      funext z
      rfl
    rw [h]
    exact hC_cont.comp h_cont_fderiv
  have h2 : ∀ (z : E r × E (m - r)), fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 =
      Module.finrank ℝ (LinearMap.range (φ z).toLinearMap) := by
    intro z
    have h_eq1 : (fderiv ℝ (fun b : E (m - r) => G (z.1, b)) z.2).toLinearMap = (φ z).toLinearMap := by
      exact our_partial_deriv G hG z
    rw [fderivRank, h_eq1]
  cases k with
  | zero =>
    have h_empty : {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < 0} = (∅ : Set (E r × E (m - r))) := by
      ext z
      simp
    rw [h_empty]
    exact isClosed_empty
  | succ k' =>
    have h3 : IsOpen {L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      rank_lower_semicontinuous k'
    have h4 : IsClosed ({L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)})ᶜ := h3.isClosed_compl
    have h5 : {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < k'.succ} =
        φ ⁻¹' ({L : (E (m - r) →L[ℝ] E (n - r)) | k' < Module.finrank ℝ (LinearMap.range L.toLinearMap)})ᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_compl_iff, Nat.lt_succ_iff]
      let a := Module.finrank ℝ (LinearMap.range (φ z).toLinearMap)
      have h_iff1 : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 ≤ k' ↔ a ≤ k' := by
        have h_eq2 : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 = a := h2 z
        exact h_eq2 ▸ Iff.rfl
      have h_iff2 : a ≤ k' ↔ ¬ (k' < a) := by
        exact Iff.symm Nat.not_lt
      have h_final : fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 ≤ k' ↔ ¬ (k' < a) := by
        rw [h_iff1, h_iff2]
      exact h_final
    rw [h5]
    exact h4.preimage hφ_cont

lemma round1_h2_eq {m n r : ℕ} (f : E m → E n)
    (U : Set (E m))
    (H : E m → E r × E (m - r))
    (G : (E r × E (m - r)) → E (n - r))
    (e : (E r × E (n - r)) ≃L[ℝ] E n)
    (heq : ∀ x ∈ U, e ((H x).1, G (H x)) = f x)
    (critSet : Set (E m))
    (S : Set (E r × E (m - r)))
    (hS : S = H '' (critSet ∩ U))
    (F : (E r × E (m - r)) → (E r × E (n - r)))
    (hF : F = fun p : (E r × E (m - r)) => (p.1, G p)) :
    f '' (critSet ∩ U) = e '' (F '' S) := by
  subst hS
  subst hF
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyU : y ∈ U := hy.2
    let z := H y
    have hz : z ∈ H '' (critSet ∩ U) := ⟨y, hy, rfl⟩
    refine ⟨(z.1, G z), ⟨z, hz, rfl⟩, ?_⟩
    exact heq y hyU
  · rintro ⟨_, ⟨z, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    have hyU : y ∈ U := hy.2
    have h : e ((H y).1, G (H y)) = f y := heq y hyU
    exact ⟨y, hy, h.symm⟩

lemma round1_critSet_measurable {m n : ℕ} (hn_pos : 0 < n) (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    MeasurableSet {x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} := by
  have h_cont : Continuous (fun x : E m => fderiv ℝ f x) :=
    hf.continuous_fderiv (by simp)
  have h2 : IsOpen {x : E m | 0 < fderivRank f x} := by
    have h_open1 : IsOpen {L : (E m →L[ℝ] E n) | 0 < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      rank_lower_semicontinuous 0
    have : {x : E m | 0 < fderivRank f x} = (fun x : E m => fderiv ℝ f x) ⁻¹' {L : (E m →L[ℝ] E n) | 0 < Module.finrank ℝ (LinearMap.range L.toLinearMap)} := by
      ext x
      simp [fderivRank]
    rw [this]
    exact h_open1.preimage h_cont
  let r' := n - 1
  have hr'_def : r' + 1 = n := by
    omega
  have h3 : IsOpen {x : E m | n ≤ fderivRank f x} := by
    have h_open2 : IsOpen {L : (E m →L[ℝ] E n) | r' < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      rank_lower_semicontinuous r'
    have h_eq1 : {L : (E m →L[ℝ] E n) | r' < Module.finrank ℝ (LinearMap.range L.toLinearMap)} = {L : (E m →L[ℝ] E n) | n ≤ Module.finrank ℝ (LinearMap.range L.toLinearMap)} := by
      ext L
      change r' < Module.finrank ℝ (LinearMap.range L.toLinearMap) ↔
        n ≤ Module.finrank ℝ (LinearMap.range L.toLinearMap)
      omega
    have : {x : E m | n ≤ fderivRank f x} = (fun x : E m => fderiv ℝ f x) ⁻¹' {L : (E m →L[ℝ] E n) | n ≤ Module.finrank ℝ (LinearMap.range L.toLinearMap)} := by
      ext x
      simp [fderivRank]
    rw [this, ←h_eq1]
    exact h_open2.preimage h_cont
  have h4 : MeasurableSet {x : E m | 0 < fderivRank f x} := h2.measurableSet
  have h5 : {x : E m | fderivRank f x < n} = ({x : E m | n ≤ fderivRank f x})ᶜ := by
    ext x
    simp
  have h6 : MeasurableSet {x : E m | fderivRank f x < n} := by
    rw [h5]
    exact h3.measurableSet.compl
  exact h4.inter h6

lemma round1_critSet_upper_rank_closed {m n : ℕ} (f : E m → E n) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    IsClosed {x : E m | fderivRank f x ≤ k} := by
  have h1 : IsOpen {L : (E m) →L[ℝ] (E n) | k < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
    rank_lower_semicontinuous k
  have h_cont : Continuous (fun x : E m => fderiv ℝ f x) := by
    exact hf.continuous_fderiv (by simp)
  have h2 : IsOpen {x : E m | k < fderivRank f x} := by
    exact h1.preimage h_cont
  have h3 : {x : E m | k < fderivRank f x}ᶜ = {x : E m | fderivRank f x ≤ k} := by
    ext x
    simp
  rw [← h3]
  exact h2.isClosed_compl

lemma round1_h_step9 {m n r : ℕ} (hnm : n < m) (hr : r < n) (g : E (m - r) → E (n - r))
    (b : E (m - r)) (h : fderivRank g b < n - r) : IsCriticalPoint g b := by
  have h1 : fderivRank g b < n - r := h
  have h2 : n - r < m - r := by omega
  have h3 : fderivRank g b < m - r := by linarith
  exact ⟨h3, h1⟩

lemma round1_h_ga_smooth {m n r : ℕ} (G : (E r × E (m - r)) → E (n - r))
    (hG : ContDiff ℝ ∞ G) (a : E r) :
    ContDiff ℝ ∞ (fun (b : E (m - r)) => G (a, b)) := by
  have h1 : ContDiff ℝ ∞ (fun (b : E (m - r)) => (a, b)) := by
    fun_prop
  exact hG.comp h1

lemma round1_h_step10 {m n r : ℕ} (hnm : n < m) (hr_pos : 0 < r) (hr_lt_n : r < n)
    (S : Set (E r × E (m - r)))
    (G : (E r × E (m - r)) → E (n - r)) (hG : ContDiff ℝ ∞ G)
    (F : (E r × E (m - r)) → (E r × E (n - r))) (hF : F = fun p => (p.1, G p))
    (hS_prop : ∀ z ∈ S, fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < n - r)
    (h_induction : ∀ (k : ℕ), k < m → ∀ (j : ℕ), ∀ (g : E k → E j), ContDiff ℝ ∞ g →
      volume (g '' {x | IsCriticalPoint g x}) = 0) :
    ∀ (a : E r), volume {c : E (n - r) | (a, c) ∈ F '' S} = 0 := by
  intro a
  let g_a : E (m - r) → E (n - r) := fun b => G (a, b)
  have hga : ContDiff ℝ ∞ g_a := round1_h_ga_smooth G hG a
  set bset : Set (E (m - r)) := {b : E (m - r) | (a, b) ∈ S} with hbset_def
  have h1 : {c : E (n - r) | (a, c) ∈ F '' S} = g_a '' bset := by
    ext c
    simp only [hF, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨z, hz, h_eq⟩
      have hz1 : z.1 = a := by
        simp at h_eq
        exact h_eq.1
      have hzc : G z = c := by
        simp at h_eq
        exact h_eq.2
      let b := z.2
      have hz_eq : z = (a, b) := by
        ext <;> simp [hz1, b]
      have h_b_in_bset : b ∈ bset := by
        simpa [hbset_def, hz_eq] using hz
      have h_goal : g_a b = c := by
        simpa [g_a, hz_eq] using hzc
      exact ⟨b, h_b_in_bset, h_goal⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(a, b), hb, by simp [g_a]⟩
  have h2 : bset ⊆ {b : E (m - r) | IsCriticalPoint g_a b} := by
    intro b hb
    have h3 : (a, b) ∈ S := hb
    have h4 : fderivRank (fun b : E (m - r) => G (( (a, b) ).1, b)) ((a, b).2) < n - r := hS_prop (a, b) h3
    have h5 : fderivRank g_a b < n - r := by simpa [g_a] using h4
    exact round1_h_step9 hnm hr_lt_n g_a b h5
  let C := {b : E (m - r) | IsCriticalPoint g_a b}
  have h3 : g_a '' bset ⊆ g_a '' C := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h4 : x ∈ C := h2 hx
    exact ⟨x, h4, rfl⟩
  have h4 : m - r < m := by omega
  have h5 : volume (g_a '' C) = 0 := h_induction (m - r) h4 (n - r) g_a hga
  have h6 : volume (g_a '' bset) = 0 := measure_mono_null h3 h5
  rw [h1]
  exact h6

lemma round1_h_fiber_null_of_null {r n : ℕ} (s : Set (E r × E (n - r))) (hs : volume s = 0) :
    ∀ᵐ (a : E r), volume ((fun c : E (n - r) => (a, c)) ⁻¹' s) = 0 := by
  let s' := MeasureTheory.toMeasurable volume s
  have hs'_meas : MeasurableSet s' := measurableSet_toMeasurable volume s
  have h1 : s ⊆ s' := subset_toMeasurable volume s
  have h2 : volume s' = 0 := by
    simpa [s'] using hs
  set f : E r → ENNReal := fun a => volume ((fun c : E (n - r) => (a, c)) ⁻¹' s') with hf_def
  let μ : MeasureTheory.Measure (E r) := volume
  let ν : MeasureTheory.Measure (E (n - r)) := volume
  letI : MeasureTheory.SFinite μ := by
    exact instSFiniteOfSigmaFinite
  letI : MeasureTheory.SFinite ν := by
    exact instSFiniteOfSigmaFinite
  have hf_meas : Measurable f := by
    exact measurable_measure_prodMk_left hs'_meas
  have h_eq_integral : (μ.prod ν) s' = ∫⁻ (a : E r), f a ∂μ := by
    exact MeasureTheory.Measure.prod_apply hs'_meas
  have h4 : ∫⁻ (a : E r), f a ∂μ = 0 := by
    rw [←h_eq_integral]
    exact h2
  have h5 : f =ᵐ[μ] 0 := (MeasureTheory.lintegral_eq_zero_iff hf_meas).mp h4
  have h6 : ∀ᵐ (a : E r), f a = 0 := h5
  filter_upwards [h6] with a ha
  have h7 : (fun c : E (n - r) => (a, c)) ⁻¹' s ⊆ (fun c : E (n - r) => (a, c)) ⁻¹' s' := by
    exact Set.preimage_mono h1
  have h8 : volume ((fun c : E (n - r) => (a, c)) ⁻¹' s) ≤ volume ((fun c : E (n - r) => (a, c)) ⁻¹' s') := measure_mono h7
  have h9 : f a = 0 := ha
  have h10 : volume ((fun c : E (n - r) => (a, c)) ⁻¹' s') = 0 := by simpa [hf_def] using h9
  have h11 : volume ((fun c : E (n - r) => (a, c)) ⁻¹' s) ≤ 0 := h8.trans h10.le
  simpa using h11

/-- Local version of fderiv_bijective_of_local_inverse: Hinv is only defined on V,
    Hinv(H(x)) = x on U, H(Hinv(z)) = z on V, but we only need bijectivity at x ∈ U. -/
lemma fderiv_bijective_local {m r : ℕ}
    (U : Set (E m)) (hU : IsOpen U)
    (V : Set (E r × E (m - r))) (hV : IsOpen V)
    (H : E m → E r × E (m - r))
    (Hinv : (E r × E (m - r)) → E m)
    (hH_diff : ContDiff ℝ ∞ H)
    (hHinv_diff : ContDiff ℝ ∞ Hinv)
    (h1 : ∀ (y : E r × E (m - r)), y ∈ V → H (Hinv y) = y)
    (h2 : ∀ (x : E m), x ∈ U → Hinv (H x) = x)
    (x : E m) (hx : x ∈ U) (hyV : H x ∈ V) :
    Function.Bijective (fderiv ℝ H x) := by
  have h_pos : 0 < (∞ : WithTop ℕ∞) := by
    exact sign_eq_one_iff.mp rfl
  let A : E m →L[ℝ] (E r × E (m - r)) := fderiv ℝ H x
  let y : E r × E (m - r) := H x
  have hyV' : y ∈ V := hyV
  let B : (E r × E (m - r)) →L[ℝ] E m := fderiv ℝ Hinv y
  have h_Hdiff : Differentiable ℝ H := hH_diff.differentiable h_pos.ne'
  have h_Hinvdiff : Differentiable ℝ Hinv := hHinv_diff.differentiable h_pos.ne'
  have h_Hdiff_at : DifferentiableAt ℝ H x := h_Hdiff.differentiableAt
  have h_Hinvdiff_at : DifferentiableAt ℝ Hinv y := h_Hinvdiff.differentiableAt
  have h_Hdiff_at2 : DifferentiableAt ℝ H (Hinv y) := by
    have h4 : Hinv y = x := h2 x hx
    rw [h4]
    exact h_Hdiff_at
  have hU_nhds : U ∈ nhds x := hU.mem_nhds hx
  have hV_nhds : V ∈ nhds y := hV.mem_nhds hyV'
  have h_id1 : ∀ᶠ (z : E m) in nhds x, (Hinv ∘ H) z = z := by
    filter_upwards [hU_nhds] with z hz
    exact h2 z hz
  have h_id2 : ∀ᶠ (z : E r × E (m - r)) in nhds y, (H ∘ Hinv) z = z := by
    filter_upwards [hV_nhds] with z hz
    exact h1 z hz
  have h_comp1 : fderiv ℝ (Hinv ∘ H) x = B.comp A := by
    rw [fderiv_comp x h_Hinvdiff_at h_Hdiff_at]
  have h4 : Hinv y = x := h2 x hx
  have h_comp2 : fderiv ℝ (H ∘ Hinv) y = A.comp B := by
    rw [fderiv_comp y h_Hdiff_at2 h_Hinvdiff_at]
    · dsimp only [A, B]
      rw [h4]
  have h_deriv1 : fderiv ℝ (Hinv ∘ H) x = ContinuousLinearMap.id ℝ (E m) := by
    have h_eq : fderiv ℝ (Hinv ∘ H) x = fderiv ℝ (fun z : E m => z) x :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h_id1
    rw [h_eq]
    simp
  have h_deriv2 : fderiv ℝ (H ∘ Hinv) y = ContinuousLinearMap.id ℝ (E r × E (m - r)) := by
    have h_eq : fderiv ℝ (H ∘ Hinv) y = fderiv ℝ (fun z : E r × E (m - r) => z) y :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) h_id2
    rw [h_eq]
    simp
  have h_eq1 : B.comp A = ContinuousLinearMap.id ℝ (E m) := by
    rw [←h_comp1, h_deriv1]
  have h_eq2 : A.comp B = ContinuousLinearMap.id ℝ (E r × E (m - r)) := by
    rw [←h_comp2, h_deriv2]
  have h_left_inverse : ∀ (z : E m), B (A z) = z := by
    intro z
    have h := congr_arg (fun (f : E m →L[ℝ] E m) => f z) h_eq1
    simpa using h
  have h_right_inverse : ∀ (z : E r × E (m - r)), A (B z) = z := by
    intro z
    have h := congr_arg (fun (f : (E r × E (m - r)) →L[ℝ] (E r × E (m - r))) => f z) h_eq2
    simpa using h
  have h_inj : Function.Injective A := by
    intro z1 z2 h
    have h5 : B (A z1) = B (A z2) := by rw [h]
    simpa [h_left_inverse] using h5
  have h_surj : Function.Surjective A := by
    intro z
    use B z
    exact h_right_inverse z
  exact ⟨h_inj, h_surj⟩

/-- The image of a locally closed set (open ∩ closed) under a continuous map
    is measurable, in second-countable locally compact T2 spaces. -/
lemma image_locally_closed_measurable {α β : Type*} [TopologicalSpace α]
    [SecondCountableTopology α] [LocallyCompactSpace α] [T2Space α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [T2Space β]
    {f : α → β} (hf : Continuous f) {V C : Set α} (hV : IsOpen V) (hC : IsClosed C) :
    MeasurableSet (f '' (V ∩ C)) := by
  by_cases h_empty : (V ∩ C) = ∅
  · rw [h_empty]
    simp
  have h_nonempty : Set.Nonempty (V ∩ C) := by
    exact Set.nonempty_iff_ne_empty.mpr h_empty
  have h1 : ∀ (x : α), x ∈ V ∩ C → ∃ (Kx : Set α), IsCompact Kx ∧ x ∈ interior Kx ∧ Kx ⊆ V := by
    intro x hx
    have hxV : x ∈ V := hx.1
    exact exists_compact_subset hV hxV
  choose K hK_compact hK_interior hK_subset using h1
  let ι := {x : α // x ∈ V ∩ C}
  let cov : ι → Set α := fun i => interior (K i.val i.property)
  have hcov_open : ∀ i : ι, IsOpen (cov i) := by
    intro i
    exact isOpen_interior
  have hcover : V ∩ C ⊆ ⋃ i : ι, cov i := by
    intro x hx
    let i : ι := ⟨x, hx⟩
    have h3 : x ∈ cov i := hK_interior i.val i.property
    exact Set.mem_iUnion.mpr ⟨i, h3⟩
  have hS_lindelof : IsLindelof (V ∩ C) := IsLindelof.of_coe
  rcases IsLindelof.elim_countable_subcover hS_lindelof cov hcov_open hcover with ⟨r, hr_count, hr_cover⟩
  have hr_nonempty : Set.Nonempty r := by
    by_contra h
    have h' : r = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at hr_cover
    simp at hr_cover
    exact h_nonempty.ne_empty (by simpa using hr_cover)
  rcases hr_count.exists_eq_range hr_nonempty with ⟨g, hg⟩
  let K' : ℕ → Set α := fun n => K (g n).val (g n).property
  let K'' : ℕ → Set α := fun n => K' n ∩ C
  have h5 : ∀ n, IsCompact (K'' n) := by
    intro n
    exact (hK_compact (g n).val (g n).property).inter_right hC
  have h6 : V ∩ C ⊆ ⋃ n, K'' n := by
    intro x hx
    have h7 : x ∈ ⋃ i ∈ r, cov i := hr_cover hx
    have h9 : ∃ n : ℕ, x ∈ cov (g n) := by
      rcases Set.mem_iUnion₂.mp h7 with ⟨i, hi_r, hxi⟩
      have h10 : i ∈ r := hi_r
      have h11 : i ∈ Set.range g := by
        rw [hg] at *
        exact h10
      rcases Set.mem_range.mp h11 with ⟨n, rfl⟩
      exact ⟨n, hxi⟩
    rcases h9 with ⟨n, hn⟩
    have h10 : x ∈ K' n := interior_subset hn
    have h11 : x ∈ C := hx.2
    have h12 : x ∈ K'' n := ⟨h10, h11⟩
    exact Set.mem_iUnion.mpr ⟨n, h12⟩
  have h7 : (⋃ n, K'' n) ⊆ V ∩ C := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
    have h8 : y ∈ K' n := hn.1
    have h9 : y ∈ V := hK_subset (g n).val (g n).property h8
    have h10 : y ∈ C := hn.2
    exact ⟨h9, h10⟩
  have h8 : V ∩ C = ⋃ n, K'' n := Set.Subset.antisymm h6 h7
  have h9 : f '' (V ∩ C) = ⋃ n, f '' (K'' n) := by
    rw [h8, Set.image_iUnion]
  rw [h9]
  apply MeasurableSet.iUnion
  intro n
  have h10 : IsCompact (f '' (K'' n)) := (h5 n).image hf
  exact h10.isClosed.measurableSet

/-- A linear equivalence preserves null sets. -/
lemma linear_equiv_preserves_null_euclid {r n : ℕ}
    (e : (E r × E (n - r)) ≃L[ℝ] E n) (s : Set (E r × E (n - r)))
    (hs : volume s = 0) : volume (e '' s) = 0 := by
  have h1 : e '' s = (e.symm) ⁻¹' s := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_rew : e.symm (e x) = x := e.symm_apply_apply x
      rw [h_rew]
      exact hx
    · intro h
      exact ⟨e.symm y, h, e.apply_symm_apply y⟩
  rw [h1]
  have h2 : volume ((e.symm) ⁻¹' s) = Measure.map (e.symm) volume s := by
    exact (e.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm
  rw [h2]
  let μ' := Measure.map e.symm volume
  let μX := (volume : Measure (E r)).prod (volume : Measure (E (n - r)))
  have h_volume_eq : (volume : Measure (E r × E (n - r))) = μX := by
    exact Measure.volume_eq_prod (E r) (E (n - r))
  letI : μ'.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map volume
  letI : IsFiniteMeasureOnCompacts μ' :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have h_eq_smul : μ' = (μ'.addHaarScalarFactor μX : ENNReal) • μX :=
    MeasureTheory.Measure.isAddLeftInvariant_eq_smul μ' μX
  have hXs : μX s = volume s := by
    have : μX = volume := h_volume_eq.symm
    rw [this]
  have h_main : μ' s = 0 := by
    calc
      μ' s
        = ((μ'.addHaarScalarFactor μX : ENNReal) • μX) s := by
          exact congr_arg (fun m : Measure (E r × E (n - r)) => m s) h_eq_smul
      _ = (μ'.addHaarScalarFactor μX : ENNReal) * μX s := by
        exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl
      _ = (μ'.addHaarScalarFactor μX : ENNReal) * volume s := by rw [hXs]
      _ = 0 := by
        rw [hs]
        simp
  exact h_main

/-- Local fact: for each point x with 0 < rank < n, there exists a neighborhood U
    of x such that f '' (S ∩ U) has volume zero, where S = {x | 0 < fderivRank f x < n}.
    Proof: apply local straightening at x, use rank formula to translate critical
    condition to partial derivative rank, apply induction on slices, then Fubini. -/
theorem positive_rank_local_fact {m n : ℕ} (hnm : 0 < n ∧ n < m)
    (f : E m → E n) (hf : ContDiff ℝ ∞ f)
    (h_induction : ∀ (k : ℕ), k < m → ∀ (j : ℕ),
      ∀ (g : E k → E j), ContDiff ℝ ∞ g →
      volume (g '' {x | IsCriticalPoint g x}) = 0)
    (x : E m) (hx : 0 < fderivRank f x ∧ fderivRank f x < n) :
    ∃ (U : Set (E m)), IsOpen U ∧ x ∈ U ∧
      volume (f '' ({x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} ∩ U)) = 0 := by
  let r := fderivRank f x
  have hr_pos : 0 < r := hx.1
  have hr_lt_n : r < n := hx.2
  let hp_rank : fderivRank f x = r := rfl
  rcases local_straightening_positive_rank f hf x hp_rank with
    ⟨U, hU, hxU, V, hV, H, hH, hH_homeo, G, hG, e, heq⟩
  rcases hH_homeo x hxU with ⟨_, ⟨Hinv, h1Hinv, hHinv_in_U, h2Hinv, hHinv_smooth⟩⟩
  let critSet : Set (E m) := {z : E m | 0 < fderivRank f z ∧ fderivRank f z < n}
  let S : Set (E r × E (m - r)) := {z ∈ V | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < n - r}
  have hHxV : H x ∈ V := (hH_homeo x hxU).1
  have h_rank_formula : ∀ (y : E m), y ∈ U →
      fderivRank f y = r + fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 := by
    intro y hy
    have hyV : H y ∈ V := (hH_homeo y hy).1
    rcases (hH_homeo y hy).2 with ⟨Hinv', h1Hinv', hHinv'_in_U, h2Hinv', hHinv'_smooth⟩
    have hyV' : H y ∈ V := hyV
    have h_bij : Function.Bijective (fderiv ℝ H y) :=
      fderiv_bijective_local U hU V hV H Hinv' hH hHinv'_smooth
        (fun z hz => h1Hinv' z hz) (fun w hw => h2Hinv' w hw) y hy hyV'
    let F : (E r × E (m - r)) → (E r × E (n - r)) := fun z => (z.1, G z)
    have hU_nhds : U ∈ nhds y := hU.mem_nhds hy
    have h_loc_eq : ∀ᶠ (z : E m) in nhds y, f z = e (F (H z)) := by
      filter_upwards [hU_nhds] with z hz
      exact (heq z hz).symm
    have h_main : fderivRank f y = r + fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 := by
      let f' : E m → E n := fun z => e (F (H z))
      have h_symm : ∀ᶠ (z : E m) in nhds y, f' z = f z := by
        filter_upwards [h_loc_eq] with z hz
        exact hz.symm
      have h_deriv_eq : fderiv ℝ f' y = fderiv ℝ f y := by
        exact Eq.symm (Filter.EventuallyEq.fderiv_eq h_loc_eq)
      have h_deriv_eq2 : fderiv ℝ f y = fderiv ℝ f' y := h_deriv_eq.symm
      have h_rank_eq : fderivRank f y = fderivRank f' y := by
        rw [fderivRank, fderivRank, h_deriv_eq2]
      rw [h_rank_eq]
      have h_eq_global : ∀ (z : E m), e ((H z).1, G (H z)) = f' z := by
        intro z
        rfl
      exact almost_done_proof_final f' G H e h_eq_global hH hG y h_bij
    exact h_main
  have h1 : H '' (critSet ∩ U) = S := by
    ext z
    simp only [S, Set.mem_sep_iff, Set.mem_image, critSet]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have h_y_in_V : H y ∈ V := (hH_homeo y hy2).1
      have h3 : fderivRank f y = r + fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 :=
        h_rank_formula y hy2
      have h4 : fderivRank f y < n := hy1.2
      have h5 : fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 < n - r := by omega
      exact ⟨h_y_in_V, h5⟩
    · rintro ⟨hzV, hz_rank⟩
      let y := Hinv z
      have hzV2 : z ∈ V := hzV
      have hHy : H y = z := h1Hinv z hzV2
      have hyU : y ∈ U := hHinv_in_U z hzV2
      have h3 : fderivRank f y = r + fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 :=
        h_rank_formula y hyU
      have h4 : fderivRank (fun b : E (m - r) => G ((H y).1, b)) (H y).2 < n - r := by
        rw [hHy]
        exact hz_rank
      have h5 : 0 < fderivRank f y ∧ fderivRank f y < n := by
        rw [h3]
        omega
      exact ⟨y, ⟨h5, hyU⟩, hHy⟩
  let F : (E r × E (m - r)) → (E r × E (n - r)) := fun p => (p.1, G p)
  have hF_def : F = fun p : (E r × E (m - r)) => (p.1, G p) := rfl
  have h2 : f '' (critSet ∩ U) = e '' (F '' S) :=
    round1_h2_eq f U H G e (fun x hx => heq x hx) critSet S h1.symm F hF_def
  let T : Set (E r × E (n - r)) := F '' S
  have hS_prop : ∀ z ∈ S, fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < n - r := by
    intro z hz
    exact hz.2
  have h3 : ∀ (a : E r), volume {c : E (n - r) | (a, c) ∈ T} = 0 :=
    round1_h_step10 hnm.2 hr_pos hr_lt_n S G hG F hF_def hS_prop h_induction
  have hS_meas : MeasurableSet S := by
    have hV_meas : MeasurableSet V := hV.measurableSet
    have h_rank_meas : MeasurableSet {z : E r × E (m - r) | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < n - r} :=
      helper_rank_fun_measurable G hG (n - r)
    exact hV_meas.inter h_rank_meas
  have hF_cont : Continuous F := by fun_prop
  let C : Set (E r × E (m - r)) := {z | fderivRank (fun b : E (m - r) => G (z.1, b)) z.2 < n - r}
  have hC_closed : IsClosed C := helper_Smeas_closed G hG (n - r)
  have hS_eq : S = V ∩ C := by
    ext z
    simp [S, C]
  have hT_meas : MeasurableSet T := by
    rw [show T = F '' (V ∩ C) from by
      rw [←hS_eq]]
    exact image_locally_closed_measurable hF_cont hV hC_closed
  have h4 : ∀ᵐ (a : E r), volume {c : E (n - r) | (a, c) ∈ T} = 0 := by
    filter_upwards with a
    exact h3 a
  have hT_null : volume T = 0 := fubini_critical_image T hT_meas h4
  have h_equiv_null : volume (e '' T) = 0 :=
    linear_equiv_preserves_null_euclid e T hT_null
  have h_final : volume (f '' (critSet ∩ U)) = 0 := by
    rw [h2]
    exact h_equiv_null
  exact ⟨U, hU, hxU, h_final⟩

end ForMathlib.Analysis.Calculus.Sard.General
