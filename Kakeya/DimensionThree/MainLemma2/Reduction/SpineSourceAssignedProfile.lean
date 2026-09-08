/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {ambient : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

open scoped Classical in
/-- Source S:5760: the assigned image of the retained leaves, not all containing nodes. -/
noncomputable def SourceThreadedTower.assignedFootprint
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (k : Nat) : Finset iota :=
  R.image (Q.place k)

open scoped Classical in
/-- Source S:5760-5763: b-ancestors of retained leaves assigned to the named a-cell. -/
noncomputable def SourceThreadedTower.retainedAssignedFibre
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota)
    (a b : Nat) (j : iota) : Finset iota :=
  (R.filter (fun i => Q.place a i = j)).image (Q.place b)

/-- The exact source D_{a,b}, formed entirely from the ancestor assignment. -/
noncomputable def SourceThreadedTower.assignedProfile
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (a b : Nat) : ENNReal :=
  (Q.assignedFootprint R a).sup (fun j =>
    Kakeya.maxDensity (Q.retainedAssignedFibre R a b j)
      (fun k => (Q.tube b k).toConvexSpaceBody))

/-- The source logarithmic profile on its own bottom radius. -/
noncomputable def SourceThreadedTower.assignedProfileExp
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (a b : Nat) : Real :=
  Real.log (max 1 (Q.assignedProfile R a b).toReal) / Real.log (1 / (delta : Real))

open scoped Classical in
/-- The source potential ranges over exactly the previously fixed M-level pairs. -/
noncomputable def SourceThreadedTower.assignedPotential
    (Q : SourceThreadedTower ambient T M C) (h : Real) (R : Finset iota) : Nat :=
  ∑ p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter (fun p => p.1 < p.2),
    Nat.ceil (Q.assignedProfileExp R p.1 p.2 / h)

open scoped Classical in
/-- A separate geometric auxiliary. It is not the source footprint. -/
noncomputable def SourceThreadedTower.geometricFootprint
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (k : Nat) : Finset iota :=
  (Q.indexSet k).filter
    (fun j => ∃ i ∈ R, (T i).toConvexSpaceBody <= (Q.tube k j).toConvexSpaceBody)

/-- A retained tower keeps the actual assignment, parent map and tube bodies.
Occupied sets may shrink. Whole original fibres at every level are not asserted. -/
structure SourceTowerRestriction
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (Q' : SourceThreadedTower R T M C) : Prop where
  subset : R <= ambient
  assignment : Q'.place = Q.place
  parent : Q'.parent = Q.parent
  tubes : Q'.tube = Q.tube
  occupied : ∀ k, k <= M -> Q'.indexSet k = Q.assignedFootprint R k
  full_retained_fibres : ∀ a b j,
    Q'.fibre a b j = Q.retainedAssignedFibre R a b j

/-- The exact retained fibre agrees with the source tower's whole-family fibre. -/
theorem source_retainedAssignedFibre_at_ambient
    (Q : SourceThreadedTower ambient T M C) (a b : Nat) (j : iota) :
    Q.retainedAssignedFibre ambient a b j = Q.fibre a b j := by
  rfl

/-- Finite image families make the source logarithm's ENNReal infinity case impossible. -/
theorem source_assignedProfile_ne_top
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (a b : Nat) :
    Q.assignedProfile R a b ≠ ⊤ := by
  classical
  apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top R.card)
  refine Finset.sup_le fun j _ => ?_
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le R _))

/-- Restriction transports the full source profile, using assignment identity. -/
theorem source_assignedProfile_restriction
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (Q' : SourceThreadedTower R T M C) (hrest : SourceTowerRestriction Q Q')
    {R' : Finset iota} (hR' : R' <= R) (a b : Nat) :
    Q'.assignedProfile R' a b = Q.assignedProfile R' a b := by
  classical
  simp only [SourceThreadedTower.assignedProfile, SourceThreadedTower.assignedFootprint,
    SourceThreadedTower.retainedAssignedFibre]
  simp_rw [hrest.assignment, hrest.tubes]

/-- The source's own fixed-M potential decreases under a retained-family restriction. -/
theorem source_assignedPotential_mono
    (Q : SourceThreadedTower ambient T M C) {R R' : Finset iota}
    (hsub : R' <= R) {h : Real} (hh : 0 < h)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    Q.assignedPotential h R' <= Q.assignedPotential h R := by
  classical
  have hprof : ∀ a b, Q.assignedProfile R' a b <= Q.assignedProfile R a b := by
    intro a b
    refine Finset.sup_le fun j hj => ?_
    refine (Kakeya.maxDensity_mono _ ?_).trans (Finset.le_sup (b := j)
      (f := fun j => Kakeya.maxDensity (Q.retainedAssignedFibre R a b j)
        (fun k => (Q.tube b k).toConvexSpaceBody)) ?_)
    · exact Finset.image_subset_image (Finset.filter_subset_filter _ hsub)
    · exact Finset.image_subset_image hsub hj
  unfold SourceThreadedTower.assignedPotential
  refine Finset.sum_le_sum fun p _ => Nat.ceil_le_ceil ?_
  refine div_le_div_of_nonneg_right ?_ hh.le
  simpa only [profileExp_of_ne_top (source_assignedProfile_ne_top Q R' p.1 p.2),
    profileExp_of_ne_top (source_assignedProfile_ne_top Q R p.1 p.2),
    SourceThreadedTower.assignedProfileExp] using
    profileExp_mono hdelta0 hdelta1 (source_assignedProfile_ne_top Q R p.1 p.2)
      (hprof p.1 p.2)

/-- Source S:5779-5781 uses a drop of at least two h, on a genuine finite pair. -/
theorem source_assignedPotential_drop
    (Q : SourceThreadedTower ambient T M C) {R R' : Finset iota}
    (hsub : R' <= R) {h : Real} (hh : 0 < h)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    {a b : Nat} (hab : a < b) (hb : b <= M)
    (hdrop : Q.assignedProfileExp R' a b + 2 * h <= Q.assignedProfileExp R a b) :
    Q.assignedPotential h R' < Q.assignedPotential h R := by
  classical
  have hprof : ∀ a b, Q.assignedProfile R' a b <= Q.assignedProfile R a b := by
    intro a b
    refine Finset.sup_le fun j hj => ?_
    refine (Kakeya.maxDensity_mono _ ?_).trans (Finset.le_sup (b := j)
      (f := fun j => Kakeya.maxDensity (Q.retainedAssignedFibre R a b j)
        (fun k => (Q.tube b k).toConvexSpaceBody)) ?_)
    · exact Finset.image_subset_image (Finset.filter_subset_filter _ hsub)
    · exact Finset.image_subset_image hsub hj
  have hexp : ∀ a b, Q.assignedProfileExp R' a b <= Q.assignedProfileExp R a b := by
    intro a b
    simpa only [profileExp_of_ne_top (source_assignedProfile_ne_top Q R' a b),
      profileExp_of_ne_top (source_assignedProfile_ne_top Q R a b),
      SourceThreadedTower.assignedProfileExp] using
      profileExp_mono hdelta0 hdelta1 (source_assignedProfile_ne_top Q R a b) (hprof a b)
  have hnn : 0 <= Q.assignedProfileExp R' a b / h := by
    refine div_nonneg ?_ hh.le
    simpa only [profileExp_of_ne_top (source_assignedProfile_ne_top Q R' a b),
      SourceThreadedTower.assignedProfileExp] using
      profileExp_nonneg hdelta0 hdelta1 (Q.assignedProfile R' a b)
  have hsplit : (Q.assignedProfileExp R' a b + 2 * h) / h =
      Q.assignedProfileExp R' a b / h + ((2 : Nat) : Real) := by
    field_simp
    ring
  have hstrict : Nat.ceil (Q.assignedProfileExp R' a b / h) <
      Nat.ceil (Q.assignedProfileExp R a b / h) := by
    have hceil := Nat.ceil_le_ceil (div_le_div_of_nonneg_right hdrop hh.le)
    rw [hsplit, Nat.ceil_add_natCast hnn] at hceil
    omega
  unfold SourceThreadedTower.assignedPotential
  refine Finset.sum_lt_sum (fun p _ => Nat.ceil_le_ceil
    (div_le_div_of_nonneg_right (hexp p.1 p.2) hh.le)) ?_
  refine ⟨(a, b), ?_, hstrict⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨by omega, by omega⟩, hab⟩

end Kakeya.ML2Core
