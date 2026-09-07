module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.DerivativeStratification
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma rank_composition_le {m n k : ℕ} (f : E m → E n) (ψ : E k → E m) (z : E m) (w : E k)
    (h_eq : ψ w = z) (hf : ContDiff ℝ ∞ f) (hψ : ContDiff ℝ ∞ ψ) :
    fderivRank (f ∘ ψ) w ≤ fderivRank f z := by
  let Df : (E m →ₗ[ℝ] E n) := (fderiv ℝ f z).toLinearMap
  let Dψ : (E k →ₗ[ℝ] E m) := (fderiv ℝ ψ w).toLinearMap
  let Dg : (E k →ₗ[ℝ] E n) := (fderiv ℝ (f ∘ ψ) w).toLinearMap
  have hf_diff : Differentiable ℝ f := by
    exact ContDiff.differentiable hf (by norm_num)
  have hψ_diff : Differentiable ℝ ψ := by
    exact ContDiff.differentiable hψ (by norm_num)
  have h1' : DifferentiableAt ℝ f (ψ w) := hf_diff (ψ w)
  have h2' : DifferentiableAt ℝ ψ w := hψ_diff w
  have h1 : HasFDerivAt f (fderiv ℝ f (ψ w)) (ψ w) := h1'.hasFDerivAt
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ w) w := h2'.hasFDerivAt
  have h3 : HasFDerivAt (f ∘ ψ) ((fderiv ℝ f (ψ w)).comp (fderiv ℝ ψ w)) w :=
    h1.comp w h2
  have h_fderiv_comp : fderiv ℝ (f ∘ ψ) w = (fderiv ℝ f (ψ w)).comp (fderiv ℝ ψ w) :=
    h3.fderiv
  have h_comp : Dg = Df.comp Dψ := by
    have h_eq2 : ψ w = z := h_eq
    simpa [Df, Dψ, Dg, h_eq2] using congr_arg ContinuousLinearMap.toLinearMap h_fderiv_comp
  have h_range : LinearMap.range Dg ≤ LinearMap.range Df := by
    rw [h_comp]
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨Dψ x, rfl⟩
  have h_main : finrank ℝ (LinearMap.range Dg) ≤ finrank ℝ (LinearMap.range Df) :=
    Submodule.finrank_mono h_range
  exact h_main

lemma h5_aux {m n : ℕ} (f : E m → E n) (x : E m) :
    fderivRank f x = 0 ↔ x ∈ flatStratum f 1 := by
  have h1 : x ∈ flatStratum f 1 ↔ iteratedFDeriv ℝ 1 f x = 0 := by
    simp only [flatStratum, Set.mem_setOf_eq]
    constructor
    · intro h
      exact h 1 ⟨by norm_num, by norm_num⟩
    · intro h ℓ hℓ
      have hℓeq : ℓ = 1 := by omega
      rw [hℓeq]
      exact h
  have h_eq : (iteratedFDeriv ℝ 1 f x = 0) ↔ (fderiv ℝ f x = 0) := by
    have h_norm : ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := norm_iteratedFDeriv_one (f := f) (x := x)
    constructor
    · intro h
      have : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by
        rw [h]
        simp
      rw [h_norm] at this
      exact norm_eq_zero.mp this
    · intro h
      have : ‖fderiv ℝ f x‖ = 0 := by
        rw [h]
        simp
      rw [←h_norm] at this
      exact norm_eq_zero.mp this
  have h_rank : (fderivRank f x = 0) ↔ (fderiv ℝ f x = 0) := by
    simp only [fderivRank]
    constructor
    · intro h
      have h' : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ := by
        exact Submodule.finrank_eq_zero.mp h
      have : (fderiv ℝ f x).toLinearMap = 0 := by
        simpa [LinearMap.range_eq_bot] using h'
      exact_mod_cast this
    · intro h
      have : (fderiv ℝ f x).toLinearMap = 0 := by exact_mod_cast h
      have h' : LinearMap.range (fderiv ℝ f x).toLinearMap = ⊥ := by
        rw [LinearMap.range_eq_bot.mpr]
        exact this
      exact Submodule.finrank_eq_zero.mpr h'
  calc
    fderivRank f x = 0 ↔ fderiv ℝ f x = 0 := h_rank
    _ ↔ iteratedFDeriv ℝ 1 f x = 0 := h_eq.symm
    _ ↔ x ∈ flatStratum f 1 := h1.symm

lemma local_stratum_image_null {m n : ℕ} (hnm : 0 < n ∧ n < m) (hm_pos : 0 < m)
    (f : E m → E n) (hf : ContDiff ℝ ∞ f) (j : ℕ) (hj : j ≥ 1)
    (h_induction : ∀ (k : ℕ), k < m → ∀ (t : ℕ),
      ∀ (g : E k → E t), ContDiff ℝ ∞ g →
      volume (g '' {x | IsCriticalPoint g x}) = 0)
    (x : E m) (hx : x ∈ (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}) :
    ∃ (N : Set (E m)), IsOpen N ∧ x ∈ N ∧
      volume (f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}) ∩ N)) = 0 := by
  have hx1 : x ∈ flatStratum f j := hx.1.1
  have hx2 : x ∉ flatStratum f (j + 1) := hx.1.2
  have hx_crit : IsCriticalPoint f x := hx.2
  rcases exists_scalar_nonzero_deriv f hf j hj x hx1 hx2 with ⟨h, hh, h1, h2⟩
  rcases hypersurface_containment hm_pos h hh x h2 with ⟨N, hN, hxN, ψ, hψ, h_sub⟩
  let S' := (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}
  have h4 : ∀ y ∈ S' ∩ N, y ∈ Set.range ψ := by
    intro y hy
    have hyS : y ∈ S' := hy.1
    have hyN : y ∈ N := hy.2
    have hy5 : y ∈ flatStratum f j := hyS.1.1
    have hhy : h y = 0 := h1 y hy5
    have h6 : y ∈ {y ∈ N | h y = 0} := ⟨hyN, hhy⟩
    exact h_sub h6
  let T : Set (E (m - 1)) := ψ ⁻¹' (S' ∩ N)
  let g : E (m - 1) → E n := f ∘ ψ
  have h51 : f '' (S' ∩ N) ⊆ g '' T := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hy_range : y ∈ Set.range ψ := h4 y hy
    rcases hy_range with ⟨w, rfl⟩
    have hw : w ∈ T := by exact hy
    exact ⟨w, hw, rfl⟩
  have h52 : g '' T ⊆ f '' (S' ∩ N) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have h6 : ψ w ∈ S' ∩ N := hw
    exact ⟨ψ w, h6, rfl⟩
  have h5 : f '' (S' ∩ N) = g '' T := Set.Subset.antisymm h51 h52
  let T' : Set (E (m - 1)) := {w : E (m - 1) | IsCriticalPoint g w}
  have h6 : T ⊆ T' := by
    intro w hw
    have h7 : ψ w ∈ S' ∩ N := hw
    let z : E m := ψ w
    have hzS : z ∈ S' := h7.1
    have hz_crit : IsCriticalPoint f z := hzS.2
    have h_rank1 : fderivRank f z < n := hz_crit.2
    have h_rank_le : fderivRank g w ≤ fderivRank f z :=
      rank_composition_le f ψ z w rfl hf hψ
    have h8 : fderivRank g w < n := by linarith
    have h9 : n ≤ m - 1 := by omega
    have h10 : fderivRank g w < m - 1 := by linarith
    exact ⟨h10, h8⟩
  have h7 : g '' T ⊆ g '' T' := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨w, h6 hw, rfl⟩
  have hψ' : ContDiff ℝ ∞ ψ := hψ
  have hg : ContDiff ℝ ∞ g := hf.comp hψ'
  have h_ind : volume (g '' T') = 0 :=
    h_induction (m - 1) (by omega) n g hg
  have h11 : volume (g '' T) = 0 := by
    exact measure_mono_null h7 h_ind
  have h12 : volume (f '' (S' ∩ N)) = 0 := by
    rw [h5]
    exact h11
  exact ⟨N, hN, hxN, h12⟩

theorem corrected_stratum_image_null {m n : ℕ} (hnm : 0 < n ∧ n < m) (hm_pos : 0 < m)
    (f : E m → E n) (hf : ContDiff ℝ ∞ f) (j : ℕ) (hj : j ≥ 1)
    (h_induction : ∀ (k : ℕ), k < m → ∀ (t : ℕ),
      ∀ (g : E k → E t), ContDiff ℝ ∞ g →
      volume (g '' {x | IsCriticalPoint g x}) = 0) :
    volume (f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) = 0 := by
  let S' := (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}
  choose N hNopen hxN hvol using fun (x : E m) (hx : x ∈ S') =>
    local_stratum_image_null hnm hm_pos f hf j hj h_induction x hx
  let U : S' → Set (E m) := fun x => N (x : E m) x.prop
  have hU_open : ∀ (x : S'), IsOpen (U x) := by
    intro x
    exact hNopen (x : E m) x.prop
  have hcover : S' ⊆ ⋃ (x : S'), U x := by
    intro y hy
    have h1 : y ∈ U (⟨y, hy⟩ : S') := hxN y hy
    exact Set.mem_iUnion.mpr ⟨(⟨y, hy⟩ : S'), h1⟩
  have hlindelof : IsLindelof S' := by
    exact IsLindelof.of_coe
  rcases IsLindelof.elim_countable_subcover hlindelof U hU_open hcover with ⟨T, hT_count, hTcover⟩
  let F : S' → Set (E n) := fun x => f '' (S' ∩ U x)
  have h1 : S' ⊆ ⋃ x ∈ T, (S' ∩ U x) := by
    intro y hy
    have h2 : y ∈ ⋃ x ∈ T, U x := hTcover hy
    rcases Set.mem_iUnion₂.mp h2 with ⟨x, hxT, hxy⟩
    have h3 : y ∈ S' ∩ U x := ⟨hy, hxy⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, h3⟩
  have h_image_eq : f '' S' ⊆ ⋃ x ∈ T, F x := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h4 : y ∈ ⋃ x ∈ T, (S' ∩ U x) := h1 hy
    rcases Set.mem_iUnion₂.mp h4 with ⟨x, hxT, hy2⟩
    have h5 : f y ∈ F x := by
      exact ⟨y, hy2, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, h5⟩
  have h_null : ∀ (x : S'), x ∈ T → volume (F x) = 0 := by
    intro x _
    exact hvol (x : E m) x.prop
  have h_countable : Set.Countable (T) := hT_count
  have h_main : volume (⋃ x ∈ T, F x) = 0 := by
    exact (measure_biUnion_null_iff hT_count).mpr h_null
  exact measure_mono_null h_image_eq h_main

/-- Lemma 12 (Image of (C_j \ C_{j+1}) ∩ critical points is null).
    For j ≥ 1, each stratum C_j \ C_{j+1}, restricted to critical points,
    is locally contained in a smooth hypersurface (Lemma 11). The restriction
    of f to this hypersurface is a C^∞ map from an (m-1)-dimensional space
    to E n. By induction in dimension m-1, the image of the critical points
    of this restriction has volume zero. By Lindelöf covering, the full
    image is null. -/
theorem stratum_image_null {m n : ℕ} (hnm : 0 < n ∧ n < m) (hm_pos : 0 < m)
    (f : E m → E n) (hf : ContDiff ℝ ∞ f) (j : ℕ) (hj : j ≥ 1)
    (h_induction : ∀ (k : ℕ), k < m → ∀ (t : ℕ),
      ∀ (g : E k → E t), ContDiff ℝ ∞ g →
      volume (g '' {x | IsCriticalPoint g x}) = 0) :
    volume (f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) = 0 :=
  corrected_stratum_image_null hnm hm_pos f hf j hj h_induction

end ForMathlib.Analysis.Calculus.Sard.General
