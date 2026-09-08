import MyLeanRepo.Kakeya.Integration.CompetitorHierarchyBridge
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ExplicitConflictDegree.Proof
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AllScaleBalancedFromDilatedCover
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData.GridAssembly
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridKRatioGate.Proof

/-!
# Exact all-real projection of the competitor grid

The competitor hierarchy is indexed from radius `1` down to radius `delta`.
The all-real WZ2 constructor consumes an increasing grid from `delta` to `1`,
so this module reverses the same stored grid.  No new coarse hierarchy and no
new fine family are chosen.

The finite-grid strong-conflict and adjacent-volume budgets remain explicit
inputs here.  The output uses lower dilation `2000`, hence the existing
balanced constructor produces the exact WZ2 dilation `7,998,000`.
-/

noncomputable section

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading

/-- The reversed competitor grid, increasing from `delta` to `1`. -/
def competitorReverseGrid
    (delta : NNReal) (N : ℕ)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (index : Fin (N + 1)) : AdmissibleScale (delta : ℝ) := by
  refine ⟨(Tube.gridScale delta N index.rev.val : NNReal), ?_, ?_⟩
  · exact_mod_cast
      (show delta ≤ Tube.gridScale delta N index.rev.val by
        calc
          delta = Tube.gridScale delta N N := by
            rw [Tube.gridScale_self delta hN]
          _ ≤ Tube.gridScale delta N index.rev.val :=
            Tube.gridScale_antitone hdelta hdeltaOne N
              (Nat.le_of_lt_succ index.rev.isLt))
  · exact_mod_cast Tube.gridScale_le_one hdeltaOne N index.rev.val

@[simp] theorem competitorReverseGrid_zero
    {delta : NNReal} {N : ℕ} (hN : 0 < N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (competitorReverseGrid delta N hN hdelta hdeltaOne 0).1 = (delta : ℝ) := by
  simp [competitorReverseGrid, Tube.gridScale_self delta hN]

@[simp] theorem competitorReverseGrid_last
    {delta : NNReal} {N : ℕ} (hN : 0 < N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (competitorReverseGrid delta N hN hdelta hdeltaOne (Fin.last N)).1 = 1 := by
  simp [competitorReverseGrid, Tube.gridScale_zero]

theorem competitorReverseGrid_strict
    {delta : NNReal} {N : ℕ} (hN : 0 < N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaStrict : delta < 1) (cut : Fin N) :
    (competitorReverseGrid delta N hN hdelta hdeltaOne
        (Fin.castSucc cut)).1 <
      (competitorReverseGrid delta N hN hdelta hdeltaOne
        (Fin.succ cut)).1 := by
  have hindex :
      (Fin.castSucc cut.rev).val < (Fin.succ cut.rev).val := by
    simp
  have hstrict := Tube.gridScale_lt_gridScale hdelta hdeltaStrict hN hindex
  simpa only [competitorReverseGrid, Fin.rev_castSucc, Fin.rev_succ,
    NNReal.coe_lt_coe] using hstrict

/-- The competitor grid is pointwise the canonical fixed-depth power grid,
viewed in increasing order. -/
theorem competitorReverseGrid_eq_canonicalIncreasingScale
    {delta : NNReal} {N : ℕ} (hN : 0 < N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaStrict : delta < 1) (index : Fin (N + 1)) :
    (competitorReverseGrid delta N hN hdelta hdeltaOne index).1 =
      ((canonicalFixedDepthPowerGrid N hN (delta : ℝ)
          (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaStrict)).increasingScale
        index).1 := by
  simp only [competitorReverseGrid, FixedDepthPowerGrid.increasingScale,
    canonicalFixedDepthPowerGrid_scale, Tube.gridScale,
    FixedDepthPowerGridTail.realScale]
  exact NNReal.coe_rpow delta _

namespace CompetitorStickyInput

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}

/-- The exact competitor node family at the lower endpoint of one reversed
grid interval. -/
def reverseGridLower
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cut : Fin N) :
    Kakeya.Streamlined.TubeFamily
      (competitorReverseGrid delta N hN hdelta hdeltaOne
        (Fin.castSucc cut)).1 := by
  change Kakeya.Streamlined.TubeFamily
    (Tube.gridScale delta N (Fin.castSucc cut).rev.val : ℝ)
  exact input.levelCoarse (Fin.castSucc cut).rev.val

/-- The same stored parent assignment, viewed at the lower endpoint of one
reversed interval with the fixed lower dilation `2000`. -/
def reverseGridCover
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cut : Fin N) :
    DilatedTubeCover 2000 input.source
      (input.reverseGridLower hN hdelta hdeltaOne cut) := by
  change DilatedTubeCover 2000 input.source
    (input.levelCoarse (Fin.castSucc cut).rev.val)
  exact input.levelCover 2000 (by norm_num)
    (Nat.le_of_lt_succ (Fin.castSucc cut).rev.isLt)

/-- The fixed assigned-fiber comparison supplied by the competitor class
brackets. -/
def reverseGridAssignedConstant : ENNReal :=
  max 1 ((C : ENNReal) ^ 2)

/-- The exact adjacent-volume budget for the reversed competitor power grid. -/
def reverseGridK (delta : NNReal) (N : ℕ) : ENNReal :=
  ENNReal.ofReal (fixedDepthPowerGridKRatio (delta : ℝ) N)

/-- Every adjacent interval of the reversed competitor grid satisfies the
volume-growth hypothesis with the single power-grid constant `reverseGridK`. -/
theorem reverseGrid_cVol_budget
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaStrict : delta < 1) (cut : Fin N) :
    2 * ENNReal.ofReal
        (cVol
          ((competitorReverseGrid delta N hN hdelta hdeltaOne
                (Fin.succ cut)).1 /
            (competitorReverseGrid delta N hN hdelta hdeltaOne
                (Fin.castSucc cut)).1)) ≤
      reverseGridK delta N := by
  let grid :=
    canonicalFixedDepthPowerGrid N hN (delta : ℝ)
      (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaStrict)
  have hgate :=
    (fixed_depth_power_grid_k_ratio_gate
      (delta := (delta : ℝ)) (N := N)
      (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne) hN grid).2.2 cut
  simpa only [reverseGridK, grid,
    competitorReverseGrid_eq_canonicalIncreasingScale
      hN hdelta hdeltaOne hdeltaStrict] using hgate

theorem one_le_reverseGridAssignedConstant :
    1 ≤ reverseGridAssignedConstant (C := C) :=
  le_max_left _ _

theorem reverseGridAssignedConstant_ne_top :
    reverseGridAssignedConstant (C := C) ≠ ⊤ := by
  simp [reverseGridAssignedConstant]

theorem reverseGridCover_assignedUniform
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cut : Fin N) :
    (input.reverseGridCover hN hdelta hdeltaOne cut).toFactoring.FibersAreCUniform
      (reverseGridAssignedConstant (C := C)) := by
  have h := input.levelStrictCover_assignedUniform
    (Nat.le_of_lt_succ (Fin.castSucc cut).rev.isLt)
  refine ⟨h.1, ?_⟩
  intro first second
  exact h.2 first second

/-- Exact package type produced by the existing finite-grid-to-all-real
constructor from the competitor hierarchy. -/
abbrev ExactAllRealPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (K : ENNReal) (degree : Fin N → ℕ) :=
  AllScaleBalancedFromDilatedCoverPackage
    input.source
    (competitorReverseGrid delta N hN hdelta hdeltaOne)
    (input.reverseGridLower hN hdelta hdeltaOne)
    (input.reverseGridCover hN hdelta hdeltaOne)
    K (reverseGridAssignedConstant (C := C)) degree

/-- Assemble the existing all-real balanced package from the exact competitor
grid.  The only remaining hypotheses are the adjacent-scale analytic budgets
required by that producer. -/
theorem exists_exactAllRealPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaStrict : delta < 1) (hN : 0 < N)
    (hsource : input.s.Nonempty)
    (K : ENNReal) (degree : Fin N → ℕ)
    (hK :
      ∀ cut : Fin N,
        2 * ENNReal.ofReal
            (cVol
              ((competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.succ cut)).1 /
                (competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.castSucc cut)).1)) ≤
          K)
    (hdegree :
      ∀ (cut : Fin N)
        (parent : Fin (input.reverseGridLower hN hdelta hdeltaOne cut).card),
        tubeConflictDegreeStrong
            (sameAxisEnlargedFamily
              (rho := (competitorReverseGrid delta N hN hdelta hdeltaOne
                (Fin.succ cut)).1)
              (input.reverseGridLower hN hdelta hdeltaOne cut))
            (Kakeya.deltaTubeVolume
              (competitorReverseGrid delta N hN hdelta hdeltaOne
                (Fin.succ cut)).1)
            K parent ≤
          degree cut) :
    Nonempty
      (input.ExactAllRealPackage hN hdelta hdeltaOne K degree) := by
  have hdeltaReal : 0 < (delta : ℝ) := by exact_mod_cast hdelta
  have hsourceWZ2 : input.source.Nonempty := by
    change 0 < input.s.card
    exact Finset.card_pos.mpr hsource
  exact
    all_scale_balanced_from_dilated_cover
      hdeltaReal hsourceWZ2 hN
      (competitorReverseGrid delta N hN hdelta hdeltaOne)
      (competitorReverseGrid_strict hN hdelta hdeltaOne hdeltaStrict)
      (competitorReverseGrid_zero hN hdelta hdeltaOne)
      (competitorReverseGrid_last hN hdelta hdeltaOne)
      (input.reverseGridLower hN hdelta hdeltaOne)
      (input.reverseGridCover hN hdelta hdeltaOne)
      (by norm_num) K (reverseGridAssignedConstant (C := C))
      hK one_le_reverseGridAssignedConstant
      reverseGridAssignedConstant_ne_top
      (input.reverseGridCover_assignedUniform hN hdelta hdeltaOne)
      degree hdegree

/--
The strong-conflict hypothesis of `exists_exactAllRealPackage` is automatic
when every lower family is pairwise essentially distinct.  The resulting
degree is the explicit support-free packing bound and depends only on the
strong parameter and the adjacent scale ratio.
-/
theorem exists_exactAllRealPackage_of_lowerED
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaStrict : delta < 1) (hN : 0 < N)
    (hsource : input.s.Nonempty)
    (Kreal : ℝ) (hKreal : 2 ≤ Kreal)
    (hK :
      ∀ cut : Fin N,
        2 * ENNReal.ofReal
            (cVol
              ((competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.succ cut)).1 /
                (competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.castSucc cut)).1)) ≤
          ENNReal.ofReal Kreal)
    (hlowerED :
      ∀ cut : Fin N,
        (input.reverseGridLower hN hdelta hdeltaOne cut).IsEssentiallyDistinct) :
    Nonempty
      (input.ExactAllRealPackage hN hdelta hdeltaOne
        (ENNReal.ofReal Kreal)
        (fun cut =>
          Nat.ceil
            (explicitConflictConstant Kreal *
              ((competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.succ cut)).1 /
                (competitorReverseGrid delta N hN hdelta hdeltaOne
                    (Fin.castSucc cut)).1) ^ 4))) := by
  let degree : Fin N → ℕ := fun cut =>
    Nat.ceil
      (explicitConflictConstant Kreal *
        ((competitorReverseGrid delta N hN hdelta hdeltaOne
              (Fin.succ cut)).1 /
          (competitorReverseGrid delta N hN hdelta hdeltaOne
              (Fin.castSucc cut)).1) ^ 4)
  apply input.exists_exactAllRealPackage
    hdelta hdeltaOne hdeltaStrict hN hsource
    (ENNReal.ofReal Kreal) degree hK
  intro cut parent
  let sigma :=
    (competitorReverseGrid delta N hN hdelta hdeltaOne
      (Fin.castSucc cut)).1
  let rho :=
    (competitorReverseGrid delta N hN hdelta hdeltaOne
      (Fin.succ cut)).1
  have hsigma : 0 < sigma := by
    exact lt_of_lt_of_le (by exact_mod_cast hdelta)
      (competitorReverseGrid delta N hN hdelta hdeltaOne
        (Fin.castSucc cut)).2.1
  have hsigmaRho : sigma ≤ rho :=
    (competitorReverseGrid_strict
      hN hdelta hdeltaOne hdeltaStrict cut).le
  have hrhoOne : rho ≤ 1 :=
    (competitorReverseGrid delta N hN hdelta hdeltaOne
      (Fin.succ cut)).2.2
  exact
    support_free_strong_enlargement_conflict_degree_explicit
      Kreal hKreal hsigma hsigmaRho hrhoOne
      (input.reverseGridLower hN hdelta hdeltaOne cut)
      (hlowerED cut) parent

theorem exactAllRealPackage_outputDilation
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (K : ENNReal) (degree : Fin N → ℕ)
    (package : input.ExactAllRealPackage hN hdelta hdeltaOne K degree) :
    package.uts.toDilatedUniformTubeStructure =
      package.uts.toDilatedUniformTubeStructure ∧
      dominatingUpperFromDilatedCoverDilation 2000 = 7998000 := by
  exact ⟨rfl, by norm_num [dominatingUpperFromDilatedCoverDilation]⟩

end CompetitorStickyInput

end Kakeya.Integration

end
