/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Basic

@[expose] public section

/-!
# Concrete Complement of k-Sphere in ℝᵐ

This file defines the standard (equatorially embedded) k-sphere Sᵏ ⊂ ℝᵐ
and its complement, together with the Mayer-Vietoris decomposition used
in the inductive computation of homology.

## Geometric setup

For k < m:
- `stdKSphere m k` = Sᵏ ⊂ ℝᵐ (unit sphere in first k+1 coordinates)
- `complementKSphere m k` = ℝᵐ ∖ Sᵏ

For the inductive Mayer-Vietoris step (k → k+1):
- `upperHemisphere m k` = closed upper hemisphere of Sᵏ⁺¹ (x_{k+1} ≥ 0)
- `lowerHemisphere m k` = closed lower hemisphere of Sᵏ⁺¹ (x_{k+1} ≤ 0)
- `compMV_U m k` = ℝᵐ ∖ (upper hemisphere)  [open]
- `compMV_V m k` = ℝᵐ ∖ (lower hemisphere)  [open]
- `compMV_U m k ∪ compMV_V m k` = ℝᵐ ∖ Sᵏ  (complement of the equator)
- `compMV_U m k ∩ compMV_V m k` = ℝᵐ ∖ Sᵏ⁺¹
-/

noncomputable section

open CategoryTheory Metric

universe w v u

namespace Geometry.Euclidean

variable {m : ℕ}

/-- The standard k-sphere Sᵏ embedded equatorially in ℝᵐ.

    This is the set of points with ‖x‖ = 1 whose coordinates from
    position k+1 onward are all zero.
    When k ≥ m, this is just the full unit sphere of ℝᵐ (degenerate case). -/
def stdKSphere (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ‖x‖ = 1 ∧ ∀ (j : Fin m), k + 1 ≤ j.val → x j = 0}

/-- The complement of the standard k-sphere in ℝᵐ. -/
def complementKSphere (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  (stdKSphere m k)ᶜ

section Hemispheres

/-- The closed upper hemisphere of S^{k+1} ⊂ ℝᵐ.

    Points on S^{k+1} with non-negative (k+1)-th coordinate.
    When k+1 ≥ m, this equals S^{k+1} (degenerate case). -/
def upperHemisphere (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x ∈ stdKSphere m (k + 1) | ∀ (j : Fin m), j.val = k + 1 → 0 ≤ x j}

/-- The closed lower hemisphere of S^{k+1} ⊂ ℝᵐ.

    Points on S^{k+1} with non-positive (k+1)-th coordinate.
    When k+1 ≥ m, this equals S^{k+1} (degenerate case). -/
def lowerHemisphere (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x ∈ stdKSphere m (k + 1) | ∀ (j : Fin m), j.val = k + 1 → x j ≤ 0}

end Hemispheres

section MVDecomposition

/-- Complement of the closed upper hemisphere of S^{k+1} (the "U" in MV). -/
def compMV_U (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  (upperHemisphere m k)ᶜ

/-- Complement of the closed lower hemisphere of S^{k+1} (the "V" in MV). -/
def compMV_V (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  (lowerHemisphere m k)ᶜ

/-- The intersection U ∩ V, which is the complement of S^{k+1}. -/
def compMV_UV (m k : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  compMV_U m k ∩ compMV_V m k

end MVDecomposition

section TopologicalProperties

/-- The standard k-sphere is a closed set. -/
lemma isClosed_stdKSphere (m k : ℕ) : IsClosed (stdKSphere m k) := by
  have h1 : IsClosed {x : EuclideanSpace ℝ (Fin m) | ‖x‖ = 1} := by
    exact isClosed_eq continuous_norm continuous_const
  have h2 : IsClosed {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), k + 1 ≤ j.val → x j = 0} := by
    have h_iInter : IsClosed (⋂ (j : Fin m), (if k + 1 ≤ j.val then {x : EuclideanSpace ℝ (Fin m) | x j = 0} else Set.univ)) := by
      apply isClosed_iInter
      intro j
      by_cases hj : k + 1 ≤ j.val
      · rw [if_pos hj]
        have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x j) := by fun_prop
        exact isClosed_eq h_cont continuous_const
      · rw [if_neg hj]
        exact isClosed_univ
    have h_eq : (⋂ (j : Fin m), (if k + 1 ≤ j.val then {x : EuclideanSpace ℝ (Fin m) | x j = 0} else Set.univ)) =
        {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), k + 1 ≤ j.val → x j = 0} := by
      ext x
      simp [Set.mem_iInter]
    rw [h_eq] at h_iInter
    exact h_iInter
  exact h1.inter h2

/-- The upper hemisphere is closed. -/
lemma isClosed_upperHemisphere (m k : ℕ) : IsClosed (upperHemisphere m k) := by
  have h1 : IsClosed (stdKSphere m (k + 1)) := isClosed_stdKSphere m (k + 1)
  have h2 : IsClosed {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), j.val = k + 1 → 0 ≤ x j} := by
    have h_iInter : IsClosed (⋂ (j : Fin m), (if j.val = k + 1 then {x : EuclideanSpace ℝ (Fin m) | 0 ≤ x j} else Set.univ)) := by
      apply isClosed_iInter
      intro j
      by_cases hj : j.val = k + 1
      · rw [if_pos hj]
        have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x j) := by fun_prop
        exact isClosed_le continuous_const h_cont
      · rw [if_neg hj]
        exact isClosed_univ
    have h_eq : (⋂ (j : Fin m), (if j.val = k + 1 then {x : EuclideanSpace ℝ (Fin m) | 0 ≤ x j} else Set.univ)) =
        {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), j.val = k + 1 → 0 ≤ x j} := by
      ext x
      simp [Set.mem_iInter]
    rw [h_eq] at h_iInter
    exact h_iInter
  exact h1.inter h2

/-- The lower hemisphere is closed. -/
lemma isClosed_lowerHemisphere (m k : ℕ) : IsClosed (lowerHemisphere m k) := by
  have h1 : IsClosed (stdKSphere m (k + 1)) := isClosed_stdKSphere m (k + 1)
  have h2 : IsClosed {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), j.val = k + 1 → x j ≤ 0} := by
    have h_iInter : IsClosed (⋂ (j : Fin m), (if j.val = k + 1 then {x : EuclideanSpace ℝ (Fin m) | x j ≤ 0} else Set.univ)) := by
      apply isClosed_iInter
      intro j
      by_cases hj : j.val = k + 1
      · rw [if_pos hj]
        have h_cont : Continuous (fun x : EuclideanSpace ℝ (Fin m) => x j) := by fun_prop
        exact isClosed_le h_cont continuous_const
      · rw [if_neg hj]
        exact isClosed_univ
    have h_eq : (⋂ (j : Fin m), (if j.val = k + 1 then {x : EuclideanSpace ℝ (Fin m) | x j ≤ 0} else Set.univ)) =
        {x : EuclideanSpace ℝ (Fin m) | ∀ (j : Fin m), j.val = k + 1 → x j ≤ 0} := by
      ext x
      simp [Set.mem_iInter]
    rw [h_eq] at h_iInter
    exact h_iInter
  exact h1.inter h2

/-- `compMV_U m k` is open (complement of a closed set). -/
lemma isOpen_compMV_U (m k : ℕ) : IsOpen (compMV_U m k) := by
  exact (isClosed_upperHemisphere m k).isOpen_compl

/-- `compMV_V m k` is open (complement of a closed set). -/
lemma isOpen_compMV_V (m k : ℕ) : IsOpen (compMV_V m k) := by
  exact (isClosed_lowerHemisphere m k).isOpen_compl

end TopologicalProperties

section DeMorganLaws

variable (k : ℕ) (h : k + 1 < m)

/-- The intersection of the two hemispheres is the equatorial k-sphere.

    upperHemisphere ∩ lowerHemisphere = stdKSphere m k -/
lemma hemispheres_inter_eq_equator (h : k + 1 < m) :
    upperHemisphere m k ∩ lowerHemisphere m k = stdKSphere m k := by
  ext x
  simp only [Set.mem_inter_iff, upperHemisphere, lowerHemisphere, Set.mem_setOf_eq]
  constructor
  · intro h_pair
    rcases h_pair with ⟨⟨h_in_sphere, h_upper⟩, ⟨_, h_lower⟩⟩
    have h_k1 : k + 1 < m := h
    let j : Fin m := ⟨k + 1, h_k1⟩
    have hj_val : j.val = k + 1 := by simp [j]
    have h_nonneg : 0 ≤ x j := h_upper j hj_val
    have h_nonpos : x j ≤ 0 := h_lower j hj_val
    have h_eq0 : x j = 0 := by linarith
    have h_main : ‖x‖ = 1 := h_in_sphere.1
    have h_tail : ∀ (j' : Fin m), k + 1 ≤ j'.val → x j' = 0 := by
      intro j' hj'
      by_cases h_eq : j'.val = k + 1
      · have h_j'_eq_j : j' = j := by
          apply Fin.ext
          rw [hj_val, h_eq]
        rw [h_j'_eq_j]
        exact h_eq0
      · have h_gt : k + 2 ≤ j'.val := by omega
        exact h_in_sphere.2 j' h_gt
    exact ⟨h_main, h_tail⟩
  · intro hx
    have h1 : x ∈ stdKSphere m (k + 1) := by
      simp only [stdKSphere, Set.mem_setOf_eq]
      constructor
      · exact hx.1
      · intro j hj
        have h' : k + 1 ≤ j.val := by omega
        exact hx.2 j h'
    have h_upper : ∀ (j : Fin m), j.val = k + 1 → 0 ≤ x j := by
      intro j hj_val
      have h_eq : x j = 0 := hx.2 j (by omega)
      rw [h_eq]
    have h_lower : ∀ (j : Fin m), j.val = k + 1 → x j ≤ 0 := by
      intro j hj_val
      have h_eq : x j = 0 := hx.2 j (by omega)
      rw [h_eq]
    exact ⟨⟨h1, h_upper⟩, ⟨h1, h_lower⟩⟩

/-- The union of the two hemispheres is the full (k+1)-sphere.

    upperHemisphere ∪ lowerHemisphere = stdKSphere m (k + 1) -/
lemma hemispheres_union_eq_sphere (h : k + 1 < m) :
    upperHemisphere m k ∪ lowerHemisphere m k = stdKSphere m (k + 1) := by
  ext x
  simp only [Set.mem_union, upperHemisphere, lowerHemisphere, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
  · intro hx
    have h_k1 : k + 1 < m := h
    let j : Fin m := ⟨k + 1, h_k1⟩
    have hj_val : j.val = k + 1 := by simp [j]
    by_cases h_nonneg : 0 ≤ x j
    · left
      refine' ⟨hx, _⟩
      intro j' hj'
      have h_j'_eq_j : j' = j := by
        apply Fin.ext
        rw [hj', hj_val]
      rw [h_j'_eq_j]
      exact h_nonneg
    · right
      have h_nonpos : x j ≤ 0 := by linarith
      refine' ⟨hx, _⟩
      intro j' hj'
      have h_j'_eq_j : j' = j := by
        apply Fin.ext
        rw [hj', hj_val]
      rw [h_j'_eq_j]
      exact h_nonpos

/-- The union of the MV open sets equals the complement of S^k.

    compMV_U m k ∪ compMV_V m k = complementKSphere m k -/
lemma compMV_union_eq (h : k + 1 < m) :
    compMV_U m k ∪ compMV_V m k = complementKSphere m k := by
  have h_de_morgan : (upperHemisphere m k)ᶜ ∪ (lowerHemisphere m k)ᶜ =
      (upperHemisphere m k ∩ lowerHemisphere m k)ᶜ := by
    rw [Set.compl_inter]
  have h_inter : upperHemisphere m k ∩ lowerHemisphere m k = stdKSphere m k :=
    hemispheres_inter_eq_equator k h
  rw [compMV_U, compMV_V, complementKSphere]
  rw [h_de_morgan, h_inter]

/-- The intersection of the MV open sets equals the complement of S^{k+1}.

    compMV_U m k ∩ compMV_V m k = complementKSphere m (k + 1) -/
lemma compMV_inter_eq (h : k + 1 < m) :
    compMV_UV m k = complementKSphere m (k + 1) := by
  have h_de_morgan : (upperHemisphere m k)ᶜ ∩ (lowerHemisphere m k)ᶜ =
      (upperHemisphere m k ∪ lowerHemisphere m k)ᶜ := by
    rw [Set.compl_union]
  have h_union : upperHemisphere m k ∪ lowerHemisphere m k = stdKSphere m (k + 1) :=
    hemispheres_union_eq_sphere k h
  rw [compMV_UV, compMV_U, compMV_V, complementKSphere]
  rw [h_de_morgan, h_union]

end DeMorganLaws

section TopCatVersions

/-- The complement of S^k in ℝ^m, as a `TopCat` object. -/
def complementKSphereTop (m k : ℕ) : TopCat :=
  TopCat.of {x : EuclideanSpace ℝ (Fin m) // x ∈ complementKSphere m k}

/-- The MV open set U (complement of upper hemisphere), as a `TopCat` object. -/
def compMV_U_top (m k : ℕ) : TopCat :=
  TopCat.of {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_U m k}

/-- The MV open set V (complement of lower hemisphere), as a `TopCat` object. -/
def compMV_V_top (m k : ℕ) : TopCat :=
  TopCat.of {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_V m k}

/-- The MV intersection U ∩ V, as a `TopCat` object. -/
def compMV_UV_top (m k : ℕ) : TopCat :=
  TopCat.of {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_UV m k}

section InclusionMaps

variable (m k : ℕ)

/-- Inclusion of U into the complement of S^k. -/
def comp_jU (h : k + 1 < m) : compMV_U_top m k ⟶ complementKSphereTop m k := by
  have h_sub : compMV_U m k ⊆ complementKSphere m k := by
    have h_eq : compMV_U m k ∪ compMV_V m k = complementKSphere m k := compMV_union_eq k h
    intro x hx
    have h_in_union : x ∈ compMV_U m k ∪ compMV_V m k := Or.inl hx
    rw [h_eq] at h_in_union
    exact h_in_union
  let f : C(↑(compMV_U_top m k), ↑(complementKSphereTop m k)) :=
    ⟨fun x => ⟨x.val, h_sub x.property⟩, by fun_prop⟩
  exact TopCat.ofHom f

/-- Inclusion of V into the complement of S^k. -/
def comp_jV (h : k + 1 < m) : compMV_V_top m k ⟶ complementKSphereTop m k := by
  have h_sub : compMV_V m k ⊆ complementKSphere m k := by
    have h_eq : compMV_U m k ∪ compMV_V m k = complementKSphere m k := compMV_union_eq k h
    intro x hx
    have h_in_union : x ∈ compMV_U m k ∪ compMV_V m k := Or.inr hx
    rw [h_eq] at h_in_union
    exact h_in_union
  let f : C(↑(compMV_V_top m k), ↑(complementKSphereTop m k)) :=
    ⟨fun x => ⟨x.val, h_sub x.property⟩, by fun_prop⟩
  exact TopCat.ofHom f

/-- Inclusion of U ∩ V into U. -/
def comp_iU (m k : ℕ) : compMV_UV_top m k ⟶ compMV_U_top m k :=
  let f : C(↑(compMV_UV_top m k), ↑(compMV_U_top m k)) :=
    ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩
  TopCat.ofHom f

/-- Inclusion of U ∩ V into V. -/
def comp_iV (m k : ℕ) : compMV_UV_top m k ⟶ compMV_V_top m k :=
  let f : C(↑(compMV_UV_top m k), ↑(compMV_V_top m k)) :=
    ⟨fun x => ⟨x.val, x.property.2⟩, by fun_prop⟩
  TopCat.ofHom f

/-- The square commutes: iU ≫ jU = iV ≫ jV. -/
lemma comp_comm (h : k + 1 < m) :
    comp_iU m k ≫ comp_jU m k h = comp_iV m k ≫ comp_jV m k h := by
  ext x
  rfl

end InclusionMaps

section UVEquivalence

variable (k : ℕ) (h : k + 1 < m)

/-- The equivalence between U ∩ V and the complement of S^{k+1}.

    This is just the identity map on the underlying elements, since
    `compMV_UV m k = complementKSphere m (k + 1)` by `compMV_inter_eq`. -/
def compMV_UV_equiv : compMV_UV_top m k ≅ complementKSphereTop m (k + 1) := by
  have h_eq : compMV_UV m k = complementKSphere m (k + 1) := compMV_inter_eq k h
  let f : C(↑(compMV_UV_top m k), ↑(complementKSphereTop m (k + 1))) :=
    ⟨fun x => ⟨x.val, h_eq ▸ x.property⟩, by fun_prop⟩
  let g : C(↑(complementKSphereTop m (k + 1)), ↑(compMV_UV_top m k)) :=
    ⟨fun x => ⟨x.val, h_eq.symm ▸ x.property⟩, by fun_prop⟩
  refine' {
    hom := TopCat.ofHom f,
    inv := TopCat.ofHom g,
    hom_inv_id := by ext x; apply Subtype.ext; rfl,
    inv_hom_id := by ext x; apply Subtype.ext; rfl
  }

end UVEquivalence

/-!
### Universe-polymorphic (ULift) versions

These versions use `ULift` to lift the concrete types to any universe `w`,
making them compatible with the universe-polymorphic singular homology functor.
-/

section ULiftVersions

/-- The complement of S^k in ℝ^m, as a universe-polymorphic `TopCat` object. -/
def complementKSphereTop' (m k : ℕ) : TopCat.{w} :=
  TopCat.of (ULift {x : EuclideanSpace ℝ (Fin m) // x ∈ complementKSphere m k})

/-- The MV open set U (complement of upper hemisphere), universe-polymorphic. -/
def compMV_U_top' (m k : ℕ) : TopCat.{w} :=
  TopCat.of (ULift {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_U m k})

/-- The MV open set V (complement of lower hemisphere), universe-polymorphic. -/
def compMV_V_top' (m k : ℕ) : TopCat.{w} :=
  TopCat.of (ULift {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_V m k})

/-- The MV intersection U ∩ V, universe-polymorphic. -/
def compMV_UV_top' (m k : ℕ) : TopCat.{w} :=
  TopCat.of (ULift {x : EuclideanSpace ℝ (Fin m) // x ∈ compMV_UV m k})

end ULiftVersions

end TopCatVersions

end Geometry.Euclidean

end section
