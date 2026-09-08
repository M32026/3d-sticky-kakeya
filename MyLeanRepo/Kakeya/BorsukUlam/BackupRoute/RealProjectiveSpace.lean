/-
# Real Projective Space and Antipodal Covering

Defines RP^n as the quotient of S^n by the antipodal action,
establishes the 2-sheeted covering map.

## Main Results
- `RPType n`: the underlying type of RP^n
- `RealProjectiveSpace n`: RP^n as a TopCat
- `quotientCovering n`: the antipodal quotient is a covering map

## Whiteprint Node
- `degree_route/real_projective_space`
-/

import Mathlib.Tactic
import Mathlib.Topology.Covering.Quotient
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology

open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open AlgebraicTopology.StdSphereHomology

noncomputable section

namespace BorsukUlam.BackupRoute

variable {n : ℕ}

/-- The antipodal equivalence relation on S^n. -/
def antipodalRel (x y : SphereType n) : Prop :=
  x = y ∨ x = antipodal n y

/-- Antipodal map is an involution. -/
lemma antipodal_involutive (x : SphereType n) : antipodal n (antipodal n x) = x := by
  apply Subtype.ext
  simp [antipodal]

lemma antipodalRel_symm {x y : SphereType n} (h : antipodalRel x y) :
    antipodalRel y x := by
  rcases h with (rfl | h)
  · exact Or.inl rfl
  · have h' : y = antipodal n x := by
      calc
        y = antipodal n (antipodal n y) := (antipodal_involutive y).symm
        _ = antipodal n x := by rw [h]
    exact Or.inr h'

lemma antipodalRel_trans {x y z : SphereType n}
    (hxy : antipodalRel x y) (hyz : antipodalRel y z) :
    antipodalRel x z := by
  rcases hxy with (rfl | hxy) <;> rcases hyz with (rfl | hyz)
  · exact Or.inl rfl
  · exact Or.inr hyz
  · exact Or.inr hxy
  · have h : x = z := by
      calc
        x = antipodal n y := hxy
        _ = antipodal n (antipodal n z) := by rw [hyz]
        _ = z := antipodal_involutive z
    exact Or.inl h

/-- Setoid instance for the antipodal relation. -/
instance antipodalSetoid : Setoid (SphereType n) where
  r := antipodalRel
  iseqv := {
    refl := fun x => Or.inl rfl,
    symm := fun {x y} h => antipodalRel_symm h,
    trans := fun {x y z} hxy hyz => antipodalRel_trans hxy hyz
  }

/-- The underlying type of real projective space RP^n. -/
def RPType (n : ℕ) : Type := Quotient (antipodalSetoid (n := n))

/-- Quotient topology on RP^n. -/
instance : TopologicalSpace (RPType n) :=
  TopologicalSpace.coinduced (Quotient.mk (antipodalSetoid (n := n))) inferInstance

/-- Real projective space RP^n as a TopCat. -/
def RealProjectiveSpace (n : ℕ) : TopCat :=
  TopCat.of (RPType n)

/-- The quotient map q : S^n → RP^n. -/
def quotientMap (n : ℕ) : SphereType n → RPType n :=
  Quotient.mk (antipodalSetoid (n := n))

/-- Continuity of the antipodal map. -/
lemma continuous_antipodal : Continuous (antipodal n) := by
  apply Continuous.subtype_mk
  exact continuous_neg.comp continuous_subtype_val

/-- The vadd action as a concrete function. -/
def fin2Vadd (g : Fin 2) (x : SphereType n) : SphereType n :=
  if g = 0 then x else antipodal n x

lemma fin2Vadd_zero (x : SphereType n) : fin2Vadd 0 x = x := by
  simp [fin2Vadd]

lemma fin2Vadd_one (x : SphereType n) : fin2Vadd 1 x = antipodal n x := by
  simp [fin2Vadd, show (1 : Fin 2) ≠ 0 from by decide]

lemma fin2Vadd_add (g₁ g₂ : Fin 2) (x : SphereType n) :
    fin2Vadd (g₁ + g₂) x = fin2Vadd g₁ (fin2Vadd g₂ x) := by
  fin_cases g₁ <;> fin_cases g₂ <;> simp [fin2Vadd_zero, fin2Vadd_one, antipodal_involutive]

/-- Fin 2 action on S^n: 0 acts as identity, 1 acts as antipodal. -/
instance : AddAction (Fin 2) (SphereType n) where
  vadd := fin2Vadd
  zero_vadd := fin2Vadd_zero
  add_vadd := fin2Vadd_add

lemma antipodalAction_continuous : ∀ (g : Fin 2), Continuous (fun x : SphereType n => g +ᵥ x) := by
  intro g
  by_cases h : g = 0
  · rw [h]
    have h' : (fun x : SphereType n => (0 : Fin 2) +ᵥ x) = _root_.id := by
      funext x; exact fin2Vadd_zero x
    rw [h']
    exact continuous_id
  · have h1 : g = 1 := by
      fin_cases g <;> tauto
    rw [h1]
    have h' : (fun x : SphereType n => (1 : Fin 2) +ᵥ x) = antipodal n := by
      funext x; exact fin2Vadd_one x
    rw [h']
    exact continuous_antipodal

/-- The quotient map identifies points in the same orbit. -/
lemma quotientMap_iff_orbit {x y : SphereType n} :
    quotientMap n x = quotientMap n y ↔ x ∈ AddAction.orbit (Fin 2) y := by
  have h1 : quotientMap n x = quotientMap n y ↔ antipodalRel x y := Quotient.eq''
  have h_vadd_def : ∀ (g : Fin 2) (z : SphereType n), g +ᵥ z = fin2Vadd g z := by
    intro g z
    rfl
  have h_iff : antipodalRel x y ↔ ∃ (g : Fin 2), g +ᵥ y = x := by
    constructor
    · intro h
      rcases h with (h_eq | h_ant)
      · have h2 : x = y := h_eq
        refine ⟨0, ?_⟩
        rw [h_vadd_def 0 y, fin2Vadd_zero y, h2]
      · have h2 : x = antipodal n y := h_ant
        refine ⟨1, ?_⟩
        rw [h_vadd_def 1 y, fin2Vadd_one y, h2]
    · rintro ⟨g, hg⟩
      have hg' : fin2Vadd g y = x := by
        rw [←h_vadd_def g y]; exact hg
      by_cases hg0 : g = 0
      · rw [hg0] at hg'
        have h : fin2Vadd 0 y = y := fin2Vadd_zero y
        rw [h] at hg'
        exact Or.inl hg'.symm
      · have hg1 : g = 1 := by fin_cases g <;> tauto
        rw [hg1] at hg'
        have h : fin2Vadd 1 y = antipodal n y := fin2Vadd_one y
        rw [h] at hg'
        exact Or.inr hg'.symm
  have h_orbit : x ∈ AddAction.orbit (Fin 2) y ↔ ∃ (g : Fin 2), g +ᵥ y = x := by
    simp [AddAction.mem_orbit_iff] <;> rfl
  rw [h1, h_iff, h_orbit]

/-- Every point has a neighborhood whose antipodal translate is disjoint. -/
lemma antipodal_disjoint (x : SphereType n) :
    ∃ (U : Set (SphereType n)), U ∈ nhds x ∧
      ∀ (g : Fin 2), ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0 := by
  have h_ne : x ≠ antipodal n x := Ne.symm (antipodal_ne_self n x)
  have h_main : ∃ (A B : Set (SphereType n)), IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ antipodal n x ∈ B ∧ Disjoint A B :=
    t2_separation h_ne
  rcases h_main with ⟨A, B, hA_open, hB_open, hxA, hxB, hdisj⟩
  let U : Set (SphereType n) := A ∩ (antipodal n ⁻¹' B)
  have hU_open : IsOpen U := hA_open.inter (hB_open.preimage continuous_antipodal)
  have hxU : x ∈ U := by
    exact ⟨hxA, hxB⟩
  have hU_nhds : U ∈ nhds x := IsOpen.mem_nhds hU_open hxU
  refine ⟨U, hU_nhds, ?_⟩
  intro g hg
  by_cases h : g = 0
  · exact h
  · have h1 : g = 1 := by fin_cases g <;> tauto
    rw [h1] at hg
    rcases hg with ⟨z, hz_image, hzU⟩
    rcases hz_image with ⟨y, hyU, rfl⟩
    have h_ayB : antipodal n y ∈ B := hyU.2
    have h_zA : antipodal n y ∈ A := hzU.1
    have h_false : False := Set.disjoint_left.mp hdisj h_zA h_ayB
    exact False.elim h_false

/-- The quotient map is coinducing (by definition of the topology). -/
lemma quotientMap_coinduced : Topology.IsCoinducing (quotientMap n) := by
  exact ⟨rfl⟩

/-- The antipodal quotient is a quotient covering map. -/
theorem quotientCovering :
    IsAddQuotientCoveringMap (quotientMap n) (Fin 2) := by
  refine' {
    toIsQuotientMap := {
      isCoinducing := quotientMap_coinduced,
      surjective := fun y => Quotient.exists_rep y
    },
    continuous_const_vadd := antipodalAction_continuous,
    apply_eq_iff_mem_orbit := quotientMap_iff_orbit,
    disjoint := antipodal_disjoint
  }

/-- The quotient map is a covering map. -/
theorem quotientIsCovering : IsCoveringMap (quotientMap n) :=
  quotientCovering.isCoveringMap

end BorsukUlam.BackupRoute
