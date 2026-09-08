import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.BalancedDominatingUpperFromDilatedCover
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentBranching
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.AllScalePiecewiseCover
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.GridPiecewiseData

/-!
# All-scale balanced structures from finite dilated covers

A finite increasing grid supplies one balanced `A`-dilated lower cover on
every adjacent interval and one upper-endpoint K-strong conflict-degree
bound.  For each intermediate radius, whole lower fibers are merged into
maximal essentially-distinct representatives.  The fine family is never
selected again.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.WithShading

namespace Kakeya.Streamlined.RandomTranslation

/-- Linear parent-conflict factor for the finite-grid dilated-cover package. -/
def allScaleBalancedFromDilatedCoverDegreeFactor
    {N : ℕ} (degree : Fin N → ℕ) : ℕ :=
  1 + ∑ cut : Fin N, degree cut

/-- Complete all-scale output from finite-grid dilated covers. -/
structure AllScaleBalancedFromDilatedCoverPackage
    {delta A : ℝ} (G : TubeFamily delta)
    {N : ℕ}
    (sigma : Fin (N + 1) → AdmissibleScale delta)
    (lower : (cut : Fin N) →
      TubeFamily (sigma (Fin.castSucc cut)).1)
    (cover : (cut : Fin N) →
      DilatedTubeCover A G (lower cut))
    (K Cbase : ENNReal)
    (degree : Fin N → ℕ) where
  outputDilation_one :
    1 ≤ dominatingUpperFromDilatedCoverDilation A
  uts :
    AssignedDilatedUniformTubeStructure
      (A := dominatingUpperFromDilatedCoverDilation A) G
  assignedUniformity_eq :
    uts.assignedUniformity =
      (allScaleBalancedFromDilatedCoverDegreeFactor degree : ENNReal) *
        Cbase
  uniformity_eq :
    uts.uniformity =
      fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation A)
          outputDilation_one *
        ((allScaleBalancedFromDilatedCoverDegreeFactor degree : ENNReal) *
          Cbase)
  bracket : AdmissibleScale delta → Fin N
  bracket_lower :
    ∀ rho,
      (sigma (Fin.castSucc (bracket rho))).1 ≤ rho.1
  bracket_upper :
    ∀ rho,
      rho.1 ≤ (sigma (Fin.succ (bracket rho))).1
  lowerFiber :
    ∀ (rho : AdmissibleScale delta)
      (_parent : Fin (uts.coarse rho).card),
      Fin (lower (bracket rho)).card
  lowerParent :
    ∀ (rho : AdmissibleScale delta),
      Fin (lower (bracket rho)).card → Fin (uts.coarse rho).card
  cover_parent :
    ∀ (rho : AdmissibleScale delta) (index : Fin G.card),
      (uts.cover rho).parent index =
        lowerParent rho ((cover (bracket rho)).parent index)
  factoringFiberIndices_lower :
    ∀ (rho : AdmissibleScale delta)
      (parent : Fin (uts.coarse rho).card),
      (cover (bracket rho)).toFactoring.fiberIndices
          (lowerFiber rho parent) ⊆
        (uts.cover rho).toFactoring.fiberIndices parent
  factoringFiberCount_lower :
    ∀ (rho : AdmissibleScale delta)
      (parent : Fin (uts.coarse rho).card),
      (cover (bracket rho)).toFactoring.fiberCount
          (lowerFiber rho parent) ≤
        (uts.cover rho).toFactoring.fiberCount parent

/-- Build an all-real-scale fixed-dilation structure from finite-grid
balanced dilated covers. -/
theorem all_scale_balanced_from_dilated_cover
    {delta A : ℝ}
    (hdelta : 0 < delta)
    {G : TubeFamily delta}
    (hG : G.Nonempty)
    {N : ℕ}
    (hN : 0 < N)
    (sigma : Fin (N + 1) → AdmissibleScale delta)
    (hmono :
      ∀ cut : Fin N,
        (sigma (Fin.castSucc cut)).1 <
          (sigma (Fin.succ cut)).1)
    (hfirst : (sigma 0).1 = delta)
    (hlast : (sigma (Fin.last N)).1 = 1)
    (lower : (cut : Fin N) →
      TubeFamily (sigma (Fin.castSucc cut)).1)
    (cover : (cut : Fin N) →
      DilatedTubeCover A G (lower cut))
    (hA : 1 ≤ A)
    (K Cbase : ENNReal)
    (hK :
      ∀ cut : Fin N,
        2 * ENNReal.ofReal
            (cVol
              ((sigma (Fin.succ cut)).1 /
                (sigma (Fin.castSucc cut)).1)) ≤
          K)
    (hCbase_one : 1 ≤ Cbase)
    (hCbase_top : Cbase ≠ ⊤)
    (huniform :
      ∀ cut, (cover cut).toFactoring.FibersAreCUniform Cbase)
    (degree : Fin N → ℕ)
    (hdegree :
      ∀ (cut : Fin N) (parent : Fin (lower cut).card),
        tubeConflictDegreeStrong
            (sameAxisEnlargedFamily
              (rho := (sigma (Fin.succ cut)).1)
              (lower cut))
            (Kakeya.deltaTubeVolume
              (sigma (Fin.succ cut)).1)
            K parent ≤
          degree cut) :
    Nonempty
      (AllScaleBalancedFromDilatedCoverPackage
        G sigma lower cover K Cbase degree) := by
  have hexists :
      ∀ rho : AdmissibleScale delta,
        ∃ cut : Fin N,
          (sigma (Fin.castSucc cut)).1 ≤ rho.1 ∧
            rho.1 ≤ (sigma (Fin.succ cut)).1 := by
    intro rho
    have hrho : delta ≤ rho.1 ∧ rho.1 ≤ 1 := rho.2
    let selectedGrid : Finset (Fin (N + 1)) :=
      Finset.univ.filter fun index =>
        (sigma index).1 ≤ rho.1
    have hzero : (0 : Fin (N + 1)) ∈ selectedGrid := by
      have h : (sigma (0 : Fin (N + 1))).1 ≤ rho.1 := by
        rw [hfirst]
        exact hrho.1
      simpa [selectedGrid] using h
    have hnonempty : selectedGrid.Nonempty := ⟨0, hzero⟩
    let maximum : Fin (N + 1) :=
      Finset.max' selectedGrid hnonempty
    have hmaximum :
        (sigma maximum).1 ≤ rho.1 :=
      (Finset.mem_filter.mp
        (Finset.max'_mem selectedGrid hnonempty)).2
    by_cases hlastIndex : maximum = Fin.last N
    · let cut : Fin N := ⟨N - 1, by omega⟩
      have hsucc : Fin.succ cut = Fin.last N := by
        apply Fin.ext
        simp [cut]
        omega
      have hrho_one : rho.1 = 1 := by
        have hleft :
            (sigma (Fin.last N)).1 ≤ rho.1 := by
          rw [← hlastIndex]
          exact hmaximum
        rw [hlast] at hleft
        linarith [hrho.2]
      refine ⟨cut, ?_, ?_⟩
      · have hstep := (hmono cut).le
        rw [hsucc, hlast] at hstep
        simpa [hrho_one] using hstep
      · rw [hsucc, hlast, hrho_one]
    · have hmaximum_lt : maximum.val < N := by
        by_contra h
        have hvalue : maximum.val = N := by omega
        have heq : maximum = Fin.last N := by
          apply Fin.ext
          simpa using hvalue
        exact hlastIndex heq
      let cut : Fin N := ⟨maximum.val, hmaximum_lt⟩
      let next : Fin (N + 1) :=
        ⟨maximum.val + 1, by omega⟩
      have hcast : Fin.castSucc cut = maximum := by
        apply Fin.ext
        rfl
      have hsucc : Fin.succ cut = next := by
        apply Fin.ext
        rfl
      have hnext_not : next ∉ selectedGrid := by
        intro hnext
        have hle : maximum ≤ next :=
          Fin.le_iff_val_le_val.mpr (Nat.le_succ _)
        have hreverse : next ≤ maximum :=
          Finset.le_max' selectedGrid next hnext
        have heq := le_antisymm hle hreverse
        have hvalue := congrArg Fin.val heq
        simp [next] at hvalue
      have hupper : rho.1 ≤ (sigma next).1 := by
        have hnot : ¬ (sigma next).1 ≤ rho.1 := by
          simpa [selectedGrid] using hnext_not
        linarith
      exact
        ⟨cut, by simpa [hcast] using hmaximum,
          by simpa [hsucc] using hupper⟩

  let bracket (rho : AdmissibleScale delta) : Fin N :=
    Classical.choose (hexists rho)
  have hbracket :
      ∀ rho,
        (sigma (Fin.castSucc (bracket rho))).1 ≤ rho.1 ∧
          rho.1 ≤ (sigma (Fin.succ (bracket rho))).1 :=
    fun rho => Classical.choose_spec (hexists rho)

  let intermediateFamily (rho : AdmissibleScale delta) :
      TubeFamily rho.1 :=
    sameAxisEnlargedFamily
      (rho := rho.1) (lower (bracket rho))
  let intermediateCover (rho : AdmissibleScale delta) :
      DilatedTubeCover A G (intermediateFamily rho) :=
    { parent := (cover (bracket rho)).parent
      parent_surjective :=
        (cover (bracket rho)).parent_surjective
      nested := fun index => by
        have hlower := (cover (bracket rho)).nested index
        have henlarge :
            dilatedTubeCarrier A
                ((lower (bracket rho)).tube
                  ((cover (bracket rho)).parent index)) ⊆
              dilatedTubeCarrier A
                ((intermediateFamily rho).tube
                  ((cover (bracket rho)).parent index)) := by
          simpa [intermediateFamily,
            sameAxisEnlargedFamily_tube] using
            dilatedTubeCarrier_subset_withRadius
              (zero_le_one.trans hA)
              (hbracket rho).1
              ((lower (bracket rho)).tube
                ((cover (bracket rho)).parent index))
        exact hlower.trans henlarge }

  have hintermediate_uniform :
      ∀ rho,
        (intermediateCover rho).toFactoring.FibersAreCUniform Cbase := by
    intro rho
    refine ⟨(huniform (bracket rho)).1, ?_⟩
    intro first second
    change
      (cover (bracket rho)).toFactoring.fiberCount first ≤
        Cbase * (cover (bracket rho)).toFactoring.fiberCount second
    exact (huniform (bracket rho)).2 first second

  have hcurrent_degree :
      ∀ (rho : AdmissibleScale delta)
        (parent : Fin (intermediateFamily rho).card),
        ((Finset.univ :
            Finset (Fin (intermediateFamily rho).card)).filter
          fun other =>
            other ≠ parent ∧
              ¬((intermediateFamily rho).tube parent).EssentiallyDistinct
                ((intermediateFamily rho).tube other)).card ≤
          degree (bracket rho) := by
    intro rho parent
    let cut := bracket rho
    change Fin (lower cut).card at parent
    let upper : TubeFamily (sigma (Fin.succ cut)).1 :=
      sameAxisEnlargedFamily
        (rho := (sigma (Fin.succ cut)).1) (lower cut)
    let current : TubeFamily rho.1 :=
      sameAxisEnlargedFamily (rho := rho.1) (lower cut)
    let currentBad : Finset (Fin (lower cut).card) :=
      Finset.univ.filter fun other =>
        other ≠ parent ∧
          ¬(current.tube parent).EssentiallyDistinct
            (current.tube other)
    have hsubset :
        currentBad.card ≤
          tubeConflictDegreeStrong upper
            (Kakeya.deltaTubeVolume
              (sigma (Fin.succ cut)).1) K parent := by
      unfold tubeConflictDegreeStrong
      rw [Finset.filter_congr_decidable]
      change currentBad.card ≤
        ((Finset.univ : Finset (Fin (lower cut).card)).filter
          fun other =>
            other ≠ parent ∧
              volume
                  ((upper.tube parent).carrier ∩
                    (upper.tube other).carrier) >
                Kakeya.deltaTubeVolume
                    (sigma (Fin.succ cut)).1 /
                  K).card
      apply Finset.card_le_card
      intro other hother
      simp only [currentBad, Finset.mem_filter,
        Finset.mem_univ, true_and] at hother ⊢
      refine ⟨hother.1, ?_⟩
      by_contra hnot
      have hstrong :
          IsKStrongEssentiallyDistinct
            (upper.tube parent) (upper.tube other)
            (Kakeya.deltaTubeVolume
              (sigma (Fin.succ cut)).1) K :=
        le_of_not_gt hnot
      have hsigma_pos :
          0 < (sigma (Fin.castSucc cut)).1 :=
        hdelta.trans_le (sigma (Fin.castSucc cut)).2.1
      have hrho_pos : 0 < rho.1 :=
        hdelta.trans_le rho.2.1
      have hratio :
          2 * ENNReal.ofReal
              (cVol
                ((sigma (Fin.succ cut)).1 / rho.1)) ≤ K := by
        have hratio_le :
            (sigma (Fin.succ cut)).1 / rho.1 ≤
              (sigma (Fin.succ cut)).1 /
                (sigma (Fin.castSucc cut)).1 := by
          exact div_le_div_of_nonneg_left
            (hdelta.trans_le
              (sigma (Fin.succ cut)).2.1).le
            (hdelta.trans_le
              (sigma (Fin.castSucc cut)).2.1)
            (hbracket rho).1
        have hcvol :
            cVol ((sigma (Fin.succ cut)).1 / rho.1) ≤
              cVol
                ((sigma (Fin.succ cut)).1 /
                  (sigma (Fin.castSucc cut)).1) := by
          by_cases heq :
              (sigma (Fin.succ cut)).1 / rho.1 =
                (sigma (Fin.succ cut)).1 /
                  (sigma (Fin.castSucc cut)).1
          · rw [heq]
          · exact
              (cVol_strict_mono
                (by
                  have hupperPos :
                      0 < (sigma (Fin.succ cut)).1 :=
                    hdelta.trans_le (sigma (Fin.succ cut)).2.1
                  positivity)
                (lt_of_le_of_ne hratio_le heq)).le
        exact
          (mul_le_mul_right (ENNReal.ofReal_le_ofReal hcvol)
            (2 : ENNReal)).trans (hK cut)
      have hed :=
        strong_ed_upper_implies_ed_at_rho
          hsigma_pos hrho_pos (hbracket rho).1
          (hbracket rho).2
          (sigma (Fin.succ cut)).2.2
          K (by simpa [cVol] using hratio)
          parent other hstrong
      exact hother.2 (by simpa [current] using hed)
    have htotal := hsubset.trans (hdegree cut parent)
    change
      ((Finset.univ : Finset (Fin (lower cut).card)).filter
        (fun other =>
          other ≠ parent ∧
            ¬(current.tube parent).EssentiallyDistinct
              (current.tube other))).card ≤ degree cut
    rw [Finset.filter_congr_decidable]
    exact htotal

  let localPackage (rho : AdmissibleScale delta) :
      BalancedDominatingUpperFromDilatedCoverPackage
        (intermediateCover rho) Cbase (degree (bracket rho)) :=
    Classical.choice
      (balanced_dominating_upper_from_dilated_cover
        (P := intermediateCover rho)
        Cbase (degree (bracket rho))
        hA hG
        (hdelta.trans_le rho.2.1)
        le_rfl rho.2.2
        (hintermediate_uniform rho)
        (hcurrent_degree rho))

  let degreeFactor :=
    allScaleBalancedFromDilatedCoverDegreeFactor degree
  let assignedUniformity : ENNReal :=
    (degreeFactor : ENNReal) * Cbase
  have hdegree_le :
      ∀ cut : Fin N, degree cut + 1 ≤ degreeFactor := by
    intro cut
    dsimp only [degreeFactor,
      allScaleBalancedFromDilatedCoverDegreeFactor]
    have hle :
        degree cut ≤ ∑ index : Fin N, degree index :=
      Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ cut)
    omega
  have hassignedUniformity_one : 1 ≤ assignedUniformity := by
    have hfactor :
        (1 : ENNReal) ≤ (degreeFactor : ENNReal) := by
      exact_mod_cast
        (show 1 ≤ degreeFactor by
          simp [degreeFactor,
            allScaleBalancedFromDilatedCoverDegreeFactor])
    calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ (degreeFactor : ENNReal) * Cbase :=
        mul_le_mul' hfactor hCbase_one
  have hassignedUniformity_top : assignedUniformity ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hCbase_top
  have houtputDilation :
      1 ≤ dominatingUpperFromDilatedCoverDilation A := by
    dsimp only [dominatingUpperFromDilatedCoverDilation]
    nlinarith
  have hassignedUniform :
      ∀ rho, (localPackage rho).cover.toFactoring.FibersAreCUniform
        assignedUniformity := by
    intro rho
    refine ⟨hassignedUniformity_one, ?_⟩
    intro first second
    have hlocal :=
      (localPackage rho).assignedUniform.2 first second
    calc
      (localPackage rho).cover.toFactoring.fiberCount first ≤
          (((degree (bracket rho) + 1 : ℕ) : ENNReal) *
            Cbase) *
            (localPackage rho).cover.toFactoring.fiberCount second :=
        hlocal
      _ ≤
          ((degreeFactor : ENNReal) * Cbase) *
            (localPackage rho).cover.toFactoring.fiberCount second := by
        gcongr
        exact_mod_cast hdegree_le (bracket rho)

  let assignedScale :
      AssignedDilatedUniformTubeStructure
        (A := dominatingUpperFromDilatedCoverDilation A) G :=
    { coarse := fun rho => (localPackage rho).upper
      cover := fun rho => (localPackage rho).cover
      assignedUniformity := assignedUniformity
      one_le_assignedUniformity := hassignedUniformity_one
      assignedUniformity_ne_top := hassignedUniformity_top
      assignedUniform := hassignedUniform
      uniformity :=
        fullContainmentBranchingLoss
            (dominatingUpperFromDilatedCoverDilation A)
            houtputDilation *
          assignedUniformity
      assignedUniformity_le_uniformity := by
        calc
          assignedUniformity = 1 * assignedUniformity := by simp
          _ ≤
              fullContainmentBranchingLoss
                  (dominatingUpperFromDilatedCoverDilation A)
                  houtputDilation *
                assignedUniformity := by
            gcongr
            exact
              one_le_fullContainmentBranchingLoss
                (dominatingUpperFromDilatedCoverDilation A)
                houtputDilation
      one_le_uniformity :=
        by
          simpa using
            mul_le_mul'
              (one_le_fullContainmentBranchingLoss
                (dominatingUpperFromDilatedCoverDilation A)
                houtputDilation)
              hassignedUniformity_one
      uniformity_ne_top :=
        ENNReal.mul_ne_top
          (fullContainmentBranchingLoss_ne_top
            (dominatingUpperFromDilatedCoverDilation A)
            houtputDilation)
          hassignedUniformity_top
      uniform := by
        intro rho
        exact
          (localPackage rho).cover
            |>.fullContainmentFibersAreCUniform_of_ownerCount
              (one_le_fullContainmentBranchingLoss
                (dominatingUpperFromDilatedCoverDilation A)
                houtputDilation)
              (hassignedUniform rho)
              (fun parent =>
                fullContainmentOwnerCount_le_branchingLoss
                  (dominatingUpperFromDilatedCoverDilation A)
                  houtputDilation
                  (hdelta.trans_le rho.2.1) rho.2.2
                  (localPackage rho).upperEssentiallyDistinct
                  (localPackage rho).cover parent)
      coarse_distinct := fun rho =>
        (localPackage rho).upperEssentiallyDistinct }

  exact ⟨{
    outputDilation_one := houtputDilation
    uts := assignedScale
    assignedUniformity_eq := rfl
    uniformity_eq := rfl
    bracket := bracket
    bracket_lower := fun rho => (hbracket rho).1
    bracket_upper := fun rho => (hbracket rho).2
    lowerFiber := fun rho parent =>
      Classical.choose
        ((localPackage rho).factoringFiberIndices_lower parent)
    lowerParent := fun rho => (localPackage rho).lowerParent
    cover_parent := fun rho index => (localPackage rho).cover_parent index
    factoringFiberIndices_lower := fun rho parent =>
      Classical.choose_spec
        ((localPackage rho).factoringFiberIndices_lower parent)
    factoringFiberCount_lower := fun rho parent =>
      by
        have hsubset := Classical.choose_spec
          ((localPackage rho).factoringFiberIndices_lower parent)
        have hcardNat := Finset.card_le_card hsubset
        have hcard :
            (intermediateCover rho).toFactoring.fiberCount
                (Classical.choose
                  ((localPackage rho).factoringFiberIndices_lower parent)) ≤
              (localPackage rho).cover.toFactoring.fiberCount parent := by
          change
            (((intermediateCover rho).toFactoring.fiberIndices
              (Classical.choose
                ((localPackage rho).factoringFiberIndices_lower parent))).card :
                ENNReal) ≤
              (((localPackage rho).cover.toFactoring.fiberIndices parent).card :
                ENNReal)
          exact_mod_cast hcardNat
        calc
          (cover (bracket rho)).toFactoring.fiberCount
                (Classical.choose
                  ((localPackage rho).factoringFiberIndices_lower parent)) =
              (intermediateCover rho).toFactoring.fiberCount
                (Classical.choose
                  ((localPackage rho).factoringFiberIndices_lower parent)) := by
            rfl
          _ ≤ (localPackage rho).cover.toFactoring.fiberCount parent := hcard
          _ = (assignedScale.cover rho).toFactoring.fiberCount parent := rfl
  }⟩

end Kakeya.Streamlined.RandomTranslation

end
