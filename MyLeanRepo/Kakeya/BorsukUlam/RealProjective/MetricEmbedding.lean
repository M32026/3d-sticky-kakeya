/-
# Veronese Embedding of RP^n into Euclidean Space

Embeds RP^n into R^{(n+1)^2} via [x] ↦ (x_i x_j), giving a metric on RP^n
via the subspace metric. This enables Mayer-Vietoris on RP^n.

## Main Results
- `veroneseMap`: continuous injective map RP^n → Euclidean space
- `veroneseHomeo`: RP^n ≃ₜ image of Veronese embedding (metric space)

## Whiteprint Node
- `real_projective_metric_embedding`
-/

import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.RealProjectiveSpace
import Mathlib.Tactic

noncomputable section

open BorsukUlam.BackupRoute
open AlgebraicTopology CategoryTheory
open AlgebraicTopology.StdSphereHomology

namespace BorsukUlam.RealProjective

variable {n : ℕ}

/-- The Veronese embedding of S^n into matrices: x ↦ (x_i x_j). -/
def veroneseFun (x : SphereType n) :
    EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1)) :=
  WithLp.toLp 2
    (fun (p : Fin (n + 1) × Fin (n + 1)) => x.val p.1 * x.val p.2)

lemma veroneseFun_apply (x : SphereType n) (i j : Fin (n + 1)) :
    (veroneseFun x) (i, j) = x.val i * x.val j := by
  rfl

lemma veroneseFun_antipodal (x : SphereType n) :
    veroneseFun (antipodal n x) = veroneseFun x := by
  apply (WithLp.equiv 2 _).injective
  funext ⟨i, j⟩
  have h1 : (antipodal n x).val = -x.val := by rfl
  simp [veroneseFun, WithLp.equiv, h1]

/-- The Veronese map descends to RP^n. -/
def veroneseMap (x : RPType n) :
    EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1)) :=
  Quotient.lift (fun x : SphereType n => veroneseFun x)
    (fun x y h => by
      rcases h with (rfl | h')
      · rfl
      · rw [h']
        exact veroneseFun_antipodal y)
    x

lemma veroneseMap_comp_quotientMap :
    veroneseMap ∘ quotientMap n = veroneseFun := by
  funext x
  rfl

lemma veroneseMap_continuous : Continuous (veroneseMap (n := n)) := by
  have hq : Topology.IsQuotientMap (quotientMap n) :=
    { isCoinducing := quotientMap_coinduced,
      surjective := fun y => Quotient.exists_rep y }
  have h : Continuous (veroneseMap ∘ quotientMap n) := by
    rw [veroneseMap_comp_quotientMap]
    have h2 : Continuous (veroneseFun : SphereType n → _) := by
      have h3 : Continuous (fun (x : SphereType n) =>
          (fun (p : Fin (n + 1) × Fin (n + 1)) => x.val p.1 * x.val p.2)) := by
        fun_prop
      let e := PiLp.continuousLinearEquiv 2 ℝ (β := fun _ : (Fin (n + 1) × Fin (n + 1)) => ℝ)
      have h4 : Continuous e.symm := e.symm.continuous
      exact h4.comp h3
    exact h2
  have h_iff : Continuous (veroneseMap (n := n)) ↔ Continuous (veroneseMap ∘ quotientMap n) := by
    exact hq.continuous_iff
  exact h_iff.mpr h

lemma veroneseMap_injective : Function.Injective (veroneseMap (n := n)) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h x =>
  induction y using Quotient.inductionOn with
  | h y =>
  have h_eq : veroneseMap ⟦x⟧ = veroneseMap ⟦y⟧ := h
  have h1 : ∀ (i j : Fin (n + 1)),
      x.val i * x.val j = y.val i * y.val j := by
    intro i j
    have h2 : (veroneseMap ⟦x⟧) (i, j) = (veroneseMap ⟦y⟧) (i, j) := by
      rw [h_eq]
    have h3 : (veroneseMap ⟦x⟧) (i, j) = x.val i * x.val j := by
      exact veroneseFun_apply x i j
    have h4 : (veroneseMap ⟦y⟧) (i, j) = y.val i * y.val j := by
      exact veroneseFun_apply y i j
    rw [h3, h4] at h2
    exact h2
  have hx_norm : ‖(x.val : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have h_exists : ∃ (k : Fin (n + 1)), x.val k ≠ 0 := by
    by_contra h2
    push Not at h2
    have h3 : x.val = 0 := by
      ext i; exact h2 i
    rw [h3] at hx_norm
    norm_num at hx_norm
  rcases h_exists with ⟨k, hxk⟩
  have hyk : y.val k ≠ 0 := by
    by_contra h4
    have h5 : x.val k * x.val k = y.val k * y.val k := h1 k k
    rw [h4] at h5
    have h6 : x.val k = 0 := by nlinarith
    exact hxk h6
  let ε : ℝ := y.val k / x.val k
  have hε2 : ε ^ 2 = 1 := by
    have h7 : x.val k * x.val k = y.val k * y.val k := h1 k k
    dsimp only [ε]
    field_simp [hxk] <;> linarith
  have hε : ε = 1 ∨ ε = -1 := by
    have h : ε ^ 2 - 1 = 0 := by linarith
    have h2 : (ε - 1) * (ε + 1) = 0 := by linarith
    have h3 : ε - 1 = 0 ∨ ε + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    rcases h3 with (h3 | h3)
    · left; linarith
    · right; linarith
  have h4 : ∀ i, x.val i = ε * y.val i := by
    intro i
    have h5 : x.val k * x.val i = y.val k * y.val i := h1 k i
    dsimp only [ε] at *
    field_simp [hxk] at h5 ⊢ <;> linarith
  rcases hε with (hε | hε)
  · have h6 : x.val = y.val := by
      ext i; rw [h4 i, hε] <;> ring
    have h7 : x = y := by
      apply Subtype.ext; exact h6
    exact Quotient.sound (Or.inl h7)
  · have h6 : x.val = -y.val := by
      ext i
      have h9 : x.val i = -y.val i := by
        rw [h4 i, hε] <;> ring
      have h10 : (-y.val) i = -y.val i := by
        have h11 : ∀ (z : EuclideanSpace ℝ (Fin (n + 1))) (j : Fin (n + 1)), (-z) j = -z j := by
          intro z j
          exact PiLp.neg_apply (fun _ => ℝ) z j
        exact h11 y.val i
      rw [h10]
      exact h9
    have h7 : x = antipodal n y := by
      apply Subtype.ext
      have h8 : (antipodal n y).val = -y.val := by rfl
      rw [h8]
      exact h6
    exact Quotient.sound (Or.inr h7)

/-- RP^n embedded in Euclidean space via Veronese embedding. -/
def RPnEmbedded (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) :=
  Set.range (veroneseMap (n := n))

/-- Equivalence between RP^n and its Veronese image. -/
def veroneseEquiv (n : ℕ) : RPType n ≃ {z // z ∈ RPnEmbedded n} :=
  { toFun := fun x => ⟨veroneseMap x, ⟨x, rfl⟩⟩
    invFun := fun z => Classical.choose z.property
    left_inv := by
      intro x
      have h : veroneseMap (Classical.choose (show veroneseMap x ∈ RPnEmbedded n from ⟨x, rfl⟩)) =
                   veroneseMap x :=
        Classical.choose_spec (show veroneseMap x ∈ RPnEmbedded n from ⟨x, rfl⟩)
      exact veroneseMap_injective h
    right_inv := by
      rintro ⟨z, hz⟩
      have h : veroneseMap (Classical.choose hz) = z := Classical.choose_spec hz
      apply Subtype.ext
      exact h }

lemma veroneseEquiv_continuous : Continuous (veroneseEquiv n) := by
  have h : Continuous (veroneseMap (n := n)) := veroneseMap_continuous
  let g : RPType n → {z // z ∈ RPnEmbedded n} :=
    fun x => ⟨veroneseMap x, ⟨x, rfl⟩⟩
  have h2 : Continuous g := Continuous.subtype_mk h (fun x => ⟨x, rfl⟩)
  exact h2

instance compactSpaceRPType : CompactSpace (RPType n) := by
  have h_sphere : CompactSpace (SphereType n) :=
    Metric.sphere.compactSpace (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
  have h_cont : Continuous (quotientMap n) := by
    exact { isOpen_preimage := fun _ hs => hs }
  have h_surj : Function.Surjective (quotientMap n) := fun y => Quotient.exists_rep y
  exact h_surj.compactSpace h_cont

/-- The Veronese embedding is a homeomorphism RP^n ≃ₜ RPnEmbedded n. -/
def veroneseHomeo (n : ℕ) :
    RPType n ≃ₜ {z // z ∈ RPnEmbedded n} :=
  have h_compact : CompactSpace (RPType n) := compactSpaceRPType
  have h_t2 : T2Space {z // z ∈ RPnEmbedded n} := by infer_instance
  (veroneseEquiv_continuous).homeoOfEquivCompactToT2

end BorsukUlam.RealProjective

end
