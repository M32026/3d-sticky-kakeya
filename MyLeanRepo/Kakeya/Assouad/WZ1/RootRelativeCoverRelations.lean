import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Root-relative relations between independent WZ1 covers

The paper repeatedly applies Proposition 5 after restricting a previously
chosen coarse configuration.  The faithful formal object is not a new
`UniformTubeStructure` rooted at that coarse family.  Instead, all selected
parents remain indexed by the original root structure, and parents at
different scales are related when they have a common active root child.

This module contains only the finite combinatorics of that replacement.  It
makes no undilated containment or transition-map assertion.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Two root-cover parents are related when they have a common active fine child. -/
def WZ1RootParentRelation
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (j : Fin (U.coarse rho).card)
    (k : Fin (U.coarse sigma).card) : Prop :=
  ∃ i : Fin F.card,
    Y.carrier i ≠ ∅ ∧
      (U.cover rho).parent i = j ∧
      (U.cover sigma).parent i = k

/-- Active root indices with two prescribed parent coordinates. -/
def wz1RootParentCell
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (j : Fin (U.coarse rho).card)
    (k : Fin (U.coarse sigma).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    Y.carrier i ≠ ∅ ∧
      (U.cover rho).parent i = j ∧
      (U.cover sigma).parent i = k

@[simp] theorem mem_wz1RootParentCell_iff
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (j : Fin (U.coarse rho).card)
    (k : Fin (U.coarse sigma).card)
    (i : Fin F.card) :
    i ∈ wz1RootParentCell U Y rho sigma j k ↔
      Y.carrier i ≠ ∅ ∧
        (U.cover rho).parent i = j ∧
        (U.cover sigma).parent i = k := by
  simp [wz1RootParentCell]

theorem wz1RootParentRelation_iff_parentCell_nonempty
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (j : Fin (U.coarse rho).card)
    (k : Fin (U.coarse sigma).card) :
    WZ1RootParentRelation U Y rho sigma j k ↔
      (wz1RootParentCell U Y rho sigma j k).Nonempty := by
  constructor
  · rintro ⟨i, hiY, hirho, hisigma⟩
    exact ⟨i, by simp [hiY, hirho, hisigma]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (mem_wz1RootParentCell_iff U Y rho sigma j k i).mp hi⟩

/-- Active fine indices assigned to one root-cover parent. -/
def wz1RootActiveFiber
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    Y.carrier i ≠ ∅ ∧ (U.cover sigma).parent i = k

@[simp] theorem mem_wz1RootActiveFiber_iff
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card)
    (i : Fin F.card) :
    i ∈ wz1RootActiveFiber U Y sigma k ↔
      Y.carrier i ≠ ∅ ∧ (U.cover sigma).parent i = k := by
  simp [wz1RootActiveFiber]

/-- `rho`-parents related to one active `sigma`-parent. -/
def wz1RootRelatedIndices
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card) :
    Finset (Fin (U.coarse rho).card) := by
  classical
  exact Finset.univ.filter fun j =>
    WZ1RootParentRelation U Y rho sigma j k

@[simp] theorem mem_wz1RootRelatedIndices_iff
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card)
    (j : Fin (U.coarse rho).card) :
    j ∈ wz1RootRelatedIndices U Y rho sigma k ↔
      WZ1RootParentRelation U Y rho sigma j k := by
  classical
  simp [wz1RootRelatedIndices]

theorem wz1RootRelatedIndices_nonempty
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card)
    (hk : (wz1RootActiveFiber U Y sigma k).Nonempty) :
    (wz1RootRelatedIndices U Y rho sigma k).Nonempty := by
  rcases hk with ⟨i, hi⟩
  have hi' := (mem_wz1RootActiveFiber_iff U Y sigma k i).mp hi
  let j := (U.cover rho).parent i
  refine ⟨j, ?_⟩
  rw [mem_wz1RootRelatedIndices_iff]
  exact ⟨i, hi'.1, rfl, hi'.2⟩

/--
One active parent fiber is the disjoint finite union of its common-child
pair cells over all related parents at another scale.
-/
theorem wz1RootActiveFiber_eq_biUnion_parentCells
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho sigma : Kakeya.Streamlined.AdmissibleScale delta)
    (k : Fin (U.coarse sigma).card) :
    wz1RootActiveFiber U Y sigma k =
      (wz1RootRelatedIndices U Y rho sigma k).biUnion fun j =>
        wz1RootParentCell U Y rho sigma j k := by
  classical
  ext i
  constructor
  · intro hi
    have hi' := (mem_wz1RootActiveFiber_iff U Y sigma k i).mp hi
    let j := (U.cover rho).parent i
    refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
    · rw [mem_wz1RootRelatedIndices_iff]
      exact ⟨i, hi'.1, rfl, hi'.2⟩
    · simp [wz1RootParentCell, j, hi'.1, hi'.2]
  · intro hi
    rcases Finset.mem_biUnion.mp hi with ⟨j, _hj, hij⟩
    have hij' :=
      (mem_wz1RootParentCell_iff U Y rho sigma j k i).mp hij
    exact
      (mem_wz1RootActiveFiber_iff U Y sigma k i).mpr
        ⟨hij'.1, hij'.2.2⟩

/-- Active root indices satisfying a finite list of independent parent constraints. -/
def wz1RootConditionalParentCell
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {m : ℕ}
    (scale :
      Fin m → Kakeya.Streamlined.AdmissibleScale delta)
    (parent :
      ∀ t, Fin (U.coarse (scale t)).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    Y.carrier i ≠ ∅ ∧
      ∀ t, (U.cover (scale t)).parent i = parent t

@[simp] theorem mem_wz1RootConditionalParentCell_iff
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {m : ℕ}
    (scale :
      Fin m → Kakeya.Streamlined.AdmissibleScale delta)
    (parent :
      ∀ t, Fin (U.coarse (scale t)).card)
    (i : Fin F.card) :
    i ∈ wz1RootConditionalParentCell U Y scale parent ↔
      Y.carrier i ≠ ∅ ∧
        ∀ t, (U.cover (scale t)).parent i = parent t := by
  simp [wz1RootConditionalParentCell]

/-- A conditional parent cell whose scales come from one fixed finite schedule. -/
def wz1RootScheduledConditionalParentCell
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {scaleCount m : ℕ}
    (schedule :
      Fin scaleCount → Kakeya.Streamlined.AdmissibleScale delta)
    (coordinate : Fin m → Fin scaleCount)
    (parent :
      ∀ t, Fin (U.coarse (schedule (coordinate t))).card) :
    Finset (Fin F.card) :=
  wz1RootConditionalParentCell U Y
    (fun t => schedule (coordinate t)) parent

@[simp] theorem mem_wz1RootScheduledConditionalParentCell_iff
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {scaleCount m : ℕ}
    (schedule :
      Fin scaleCount → Kakeya.Streamlined.AdmissibleScale delta)
    (coordinate : Fin m → Fin scaleCount)
    (parent :
      ∀ t, Fin (U.coarse (schedule (coordinate t))).card)
    (i : Fin F.card) :
    i ∈ wz1RootScheduledConditionalParentCell
        U Y schedule coordinate parent ↔
      Y.carrier i ≠ ∅ ∧
        ∀ t,
          (U.cover (schedule (coordinate t))).parent i =
            parent t := by
  exact mem_wz1RootConditionalParentCell_iff
    U Y (fun t => schedule (coordinate t)) parent i

/--
Every nonempty active parent cell involving at most `depth + 1` coordinates
from one caller-supplied finite schedule has comparable cardinality.

The finite schedule is API-critical.  WZ1 uses only finitely many scales in
each invocation; it does not simultaneously regularize the continuum of all
admissible radii.
-/
def WZ1RootScheduledConditionalUniformity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (depth : ℕ)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    {scaleCount : ℕ}
    (schedule :
      Fin scaleCount → Kakeya.Streamlined.AdmissibleScale delta)
    (C : ENNReal) : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → m ≤ depth + 1 →
    ∀ (coordinate : Fin m → Fin scaleCount)
      (parent parent' :
        ∀ t, Fin (U.coarse (schedule (coordinate t))).card),
      (wz1RootScheduledConditionalParentCell
        U Y schedule coordinate parent).Nonempty →
      (wz1RootScheduledConditionalParentCell
        U Y schedule coordinate parent').Nonempty →
      ((wz1RootScheduledConditionalParentCell
          U Y schedule coordinate parent).card : ENNReal) ≤
        C *
          (wz1RootScheduledConditionalParentCell
            U Y schedule coordinate parent').card

end Kakeya.Assouad
