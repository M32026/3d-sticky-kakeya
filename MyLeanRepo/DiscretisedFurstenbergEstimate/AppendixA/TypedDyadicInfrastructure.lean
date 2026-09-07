module

/-
  Typed dyadic QTTC: Quantitative Thick Tube Cover using sourceParent.

  Uses `sourceParent` = `coarseTubeToM` (floor division), which gives
  GENUINE dyadic containment: the fine tube's parameter cell is a subset
  of the coarse parent's parameter cell.

  NOT `coarseImage` (nearest-rounding), which does NOT give containment.

  Main results:
  - `sourceParent`: floor-division parent (genuine containment)
  - `pointCoarseFamily`, `childCount`, `childCount_partition`
  - `globalCoarseFamily`, `globalFiber`, `globalChildCount`
  - `globalChildCount_partition`: Σ globalChildCount = |T_global|
  - `globalIncidenceCount` (incidence-weighted, distinct from globalChildCount)
  - `canonicalRep`, `canonicalRep_injective`
  - `pointFiber`, `pointFiber_partition`
  - `fine_to_coarse_affineBound`: geometric adapter (nearestCoarseImage only)

  Whiteprint node: appendix_a_alternative / typed_dyadic_qttc
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoarseSSetProperty
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.InductionOnScales
  (coarseTubeToM refinementFactor)

/-! ========================================================================
   Source parent: floor-division gives genuine dyadic containment
   ======================================================================== -/

/-- The source (containment) parent: floor-divide fine tube indices by
    the refinement factor. Gives genuine dyadic containment. -/
def sourceParent {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) : DyadicTube m :=
  coarseTubeToM hnm T


/-- Refinement factor is positive. -/
lemma refinementFactor_pos' {n m : ℕ} (hnm : m ≤ n) :
    0 < (refinementFactor n m : ℤ) := by
  have h : 0 < refinementFactor n m := by
    dsimp only [refinementFactor]
    positivity
  exact_mod_cast h

/-- Integer division criterion: for `k > 0`,
    `a / k = c ↔ c * k ≤ a ∧ a < (c + 1) * k`. -/
lemma int_ediv_criterion {a c k : ℤ} (hk : 0 < k) :
    a / k = c ↔ c * k ≤ a ∧ a < (c + 1) * k := by
  have h_alg : (a % k) + k * (a / k) = a ∧ 0 ≤ (a % k) ∧ (a % k) < k := by
    have h₁ : (a / k = a / k ∧ a % k = a % k) ↔
        (a % k) + k * (a / k) = a ∧ 0 ≤ (a % k) ∧ (a % k) < |k| :=
      Int.ediv_emod_unique'' (show (k : ℤ) ≠ 0 from by linarith)
    have h₂ := h₁.mp ⟨rfl, rfl⟩
    simpa [abs_of_pos hk] using h₂
  rcases h_alg with ⟨h_eq, h_nonneg, h_lt⟩
  constructor
  · intro h
    rw [h] at h_eq
    constructor
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    have h3 : c ≤ a / k := by
      by_contra h4
      have h5 : a / k < c := by linarith
      nlinarith
    have h4 : a / k ≤ c := by
      by_contra h5
      have h6 : c < a / k := by linarith
      nlinarith
    have h5 : a / k = c := by linarith
    exact h5

/-- Source parent containment criterion:
    `sourceParent hnm T = U` iff T's integer indices lie in U's block
    in both coordinates (exact dyadic containment). -/
lemma sourceParent_containment {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m) :
    sourceParent hnm T = U ↔
      U.a * (refinementFactor n m : ℤ) ≤ T.a ∧
      T.a < (U.a + 1) * (refinementFactor n m : ℤ) ∧
      U.b * (refinementFactor n m : ℤ) ≤ T.b ∧
      T.b < (U.b + 1) * (refinementFactor n m : ℤ) := by
  let k : ℤ := refinementFactor n m
  have hk_pos : 0 < k := refinementFactor_pos' hnm
  have ha : (T.a / k) = U.a ↔
      U.a * k ≤ T.a ∧ T.a < (U.a + 1) * k :=
    int_ediv_criterion hk_pos
  have hb : (T.b / k) = U.b ↔
      U.b * k ≤ T.b ∧ T.b < (U.b + 1) * k :=
    int_ediv_criterion hk_pos
  dsimp only [sourceParent, coarseTubeToM]
  constructor
  · intro h
    have h_eq_a : (T.a / k) = U.a := by
      exact congr_arg (fun (x : DyadicTube m) => x.a) h
    have h_eq_b : (T.b / k) = U.b := by
      exact congr_arg (fun (x : DyadicTube m) => x.b) h
    rcases ha.mp h_eq_a with ⟨ha1, ha2⟩
    rcases hb.mp h_eq_b with ⟨hb1, hb2⟩
    exact ⟨ha1, ha2, hb1, hb2⟩
  · rintro ⟨ha1, ha2, hb1, hb2⟩
    have h_eq_a : (T.a / k) = U.a := ha.mpr ⟨ha1, ha2⟩
    have h_eq_b : (T.b / k) = U.b := hb.mpr ⟨hb1, hb2⟩
    have h_goal : (T.a / k) = U.a ∧ (T.b / k) = U.b := ⟨h_eq_a, h_eq_b⟩
    exact InductionOnScales.DyadicTube.eq_iff.mpr h_goal

end DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
