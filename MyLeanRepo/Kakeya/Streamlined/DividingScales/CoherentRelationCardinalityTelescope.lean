import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationCardinalityComparability
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationReferenceDensityTelescope

/-!
# Coherent hierarchy socket for the relation-cardinality telescope

The independent cover system records a parent of every bottom tube at every
grid scale, but it does not require those parent assignments to factor through
one another.  The smallest additional datum used here is a compatible
transition map from every finer level of one selected subchain to every
coarser level:

```text
transition (fine parent of a bottom tube) = its coarse parent.
```

This is the formal version of the v4/v5 coherent hierarchy's transitive
assigned-parent tree.  It rules out the remerging counterexample in which two
middle parents have the same two fine parents.

The module first proves the exact descendant-fiber identity.  Subsequent
lemmas turn that identity into the product lower bound for minimum branching
cardinalities, then combine it with the already proved edgewise conditional
uniformity and reference-density scale telescope.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
One fixed compatible parent hierarchy on the entire distinguished grid.

This is the consumer-facing projection of the v5 canonical tree.  A richer
producer may additionally store literal parent containment, transition
composition, occupied-node pruning data, and profile regularity; localized
composition only needs these compatible parent transitions.
-/
structure CoherentGridParentHierarchy
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one) where
  transition :
    ∀ coarse fine : UniformScaleIndex delta, coarse ≤ fine →
      Fin (U.coarse fine).card → Fin (U.coarse coarse).card
  parent_compatible :
    ∀ (coarse fine : UniformScaleIndex delta) (h : coarse ≤ fine)
      (original : Fin F.card),
      transition coarse fine h ((U.cover fine).parent original) =
        (U.cover coarse).parent original

/--
Parent transitions along one grid subchain, compatible with the ambient
bottom-tube parent assignments.

Only occupied parents are used downstream.  Requiring compatibility for all
bottom tubes is the natural output of the fixed canonical hierarchy proposed
in `77fix_v4.md`.
-/
structure CoherentGridSubchainParentHierarchy
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one)
    {J : ℕ} (chain : GridIndexSubchain delta J) where
  transition :
    ∀ coarse fine : Fin (J + 1), coarse ≤ fine →
      Fin (U.coarse (chain.index fine.val)).card →
        Fin (U.coarse (chain.index coarse.val)).card
  parent_compatible :
    ∀ (coarse fine : Fin (J + 1)) (h : coarse ≤ fine)
      (original : Fin F.card),
      transition coarse fine h
          ((U.cover (chain.index fine.val)).parent original) =
        (U.cover (chain.index coarse.val)).parent original

namespace CoherentGridParentHierarchy

variable {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := localC) F hdelta_le_one}

/--
Compatibility with the surjective leaf-parent map forces every same-level
transition to be the identity.
-/
lemma transition_refl
    (H : CoherentGridParentHierarchy U)
    (level : UniformScaleIndex delta)
    (parent : Fin (U.coarse level).card) :
    H.transition level level le_rfl parent = parent := by
  rcases (U.cover level).parent_surjective parent with
    ⟨original, horiginal⟩
  rw [← horiginal]
  exact H.parent_compatible level level le_rfl original

/--
Compatibility with the surjective leaf-parent maps also forces long-range
transitions to compose.  Thus a producer need not store a separate
transitivity field.
-/
lemma transition_comp
    (H : CoherentGridParentHierarchy U)
    (coarse middle fine : UniformScaleIndex delta)
    (hcoarseMiddle : coarse ≤ middle)
    (hmiddleFine : middle ≤ fine)
    (parent : Fin (U.coarse fine).card) :
    H.transition coarse middle hcoarseMiddle
        (H.transition middle fine hmiddleFine parent) =
      H.transition coarse fine
        (hcoarseMiddle.trans hmiddleFine) parent := by
  rcases (U.cover fine).parent_surjective parent with
    ⟨original, horiginal⟩
  rw [← horiginal]
  rw [H.parent_compatible middle fine hmiddleFine original]
  rw [H.parent_compatible coarse middle hcoarseMiddle original]
  rw [H.parent_compatible coarse fine
    (hcoarseMiddle.trans hmiddleFine) original]

/-- Restrict one fixed grid hierarchy to an arbitrary increasing subchain. -/
def restrictToSubchain
    (H : CoherentGridParentHierarchy U)
    {J : ℕ} (chain : GridIndexSubchain delta J) :
    CoherentGridSubchainParentHierarchy U chain where
  transition coarse fine hcoarseFine :=
    H.transition
      (chain.index coarse.val)
      (chain.index fine.val)
      (chain.index_le_of_le
        (show coarse.val ≤ fine.val by exact hcoarseFine)
        (show fine.val ≤ J by omega))
  parent_compatible coarse fine hcoarseFine original := by
    exact H.parent_compatible
      (chain.index coarse.val)
      (chain.index fine.val)
      (chain.index_le_of_le
        (show coarse.val ≤ fine.val by exact hcoarseFine)
        (show fine.val ≤ J by omega))
      original

end CoherentGridParentHierarchy

namespace CoherentGridSubchainParentHierarchy

variable {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := localC) F hdelta_le_one}
variable {J : ℕ} {chain : GridIndexSubchain delta J}

/-- Parents at one level descending from the represented root endpoint cell. -/
def descendantIndices
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (level : Fin (J + 1)) :
    Finset (Fin (U.coarse (chain.index level.val)).card) :=
  P.relationIndices i (chain.index level.val) (chain.index 0)

/-- Every descendant parent maps to a descendant parent at any coarser
position. -/
lemma transition_mem_descendantIndices
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (coarse fine : Fin (J + 1))
    (hcoarseFine : coarse ≤ fine)
    (j : Fin (U.coarse (chain.index fine.val)).card)
    (hj : j ∈ H.descendantIndices P i fine) :
    H.transition coarse fine hcoarseFine j ∈
      H.descendantIndices P i coarse := by
  rcases
      (P.mem_relationIndices_iff
        i (chain.index fine.val) (chain.index 0) j).mp hj with
    ⟨original, hhistory, hroot, hfine⟩
  apply (P.mem_relationIndices_iff
    i (chain.index coarse.val) (chain.index 0)
      (H.transition coarse fine hcoarseFine j)).mpr
  refine ⟨original, hhistory, hroot, ?_⟩
  rw [← H.parent_compatible coarse fine hcoarseFine original]
  exact congrArg (H.transition coarse fine hcoarseFine) hfine

/-- The descendant transition is surjective between occupied descendant
sets. -/
lemma transition_surjective_on_descendantIndices
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (coarse fine : Fin (J + 1))
    (hcoarseFine : coarse ≤ fine) :
    ∀ j ∈ H.descendantIndices P i coarse,
      ∃ j' ∈ H.descendantIndices P i fine,
        H.transition coarse fine hcoarseFine j' = j := by
  intro j hj
  rcases
      (P.mem_relationIndices_iff
        i (chain.index coarse.val) (chain.index 0) j).mp hj with
    ⟨original, hhistory, hroot, hcoarse⟩
  let j' := (U.cover (chain.index fine.val)).parent original
  refine ⟨j', ?_, ?_⟩
  · apply (P.mem_relationIndices_iff
      i (chain.index fine.val) (chain.index 0) j').mpr
    exact ⟨original, hhistory, hroot, rfl⟩
  · rw [H.parent_compatible coarse fine hcoarseFine original]
    exact hcoarse

/--
Inside one represented root endpoint cell, the fiber of the coherent
transition from `fine` to `coarse` is exactly the represented relation family
from the fine level to the coarse parent represented by `representative`.
-/
lemma transitionFiber_eq_relationIndices
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (i representative : Fin F.card)
    (coarse fine : Fin (J + 1))
    (hcoarseFine : coarse ≤ fine)
    (hrepresentativeHistory :
      representative ∈
        conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i))
    (hrepresentativeRoot :
      (U.cover (chain.index 0)).parent representative =
        (U.cover (chain.index 0)).parent i) :
    (H.descendantIndices P i fine).filter
        (fun j =>
          H.transition coarse fine hcoarseFine j =
            (U.cover (chain.index coarse.val)).parent representative) =
      P.relationIndices representative
        (chain.index fine.val) (chain.index coarse.val) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hjdescendant, hjtransition⟩
    rcases
        (P.mem_relationIndices_iff
          i (chain.index fine.val) (chain.index 0) j).mp
          hjdescendant with
      ⟨original, hhistory, hroot, hfine⟩
    rw [P.mem_relationIndices_iff]
    refine ⟨original, ?_, ?_, hfine⟩
    · have hrepresentativeParent :
          P.parentOf representative = P.parentOf i := by
        funext t
        have hrepresentative :=
          (mem_conditionalParentCell_iff
            U.coarse U.cover P.scale (P.parentOf i) representative).mp
              hrepresentativeHistory t
        simp only [FrostmanConditionalFactorScope.parentOf]
        exact hrepresentative
      simpa [hrepresentativeParent] using hhistory
    · have htransitionOriginal :
          H.transition coarse fine hcoarseFine j =
            (U.cover (chain.index coarse.val)).parent original := by
        calc
          H.transition coarse fine hcoarseFine j
              =
            H.transition coarse fine hcoarseFine
              ((U.cover (chain.index fine.val)).parent original) :=
                congrArg (H.transition coarse fine hcoarseFine)
                  hfine.symm
          _ = (U.cover (chain.index coarse.val)).parent original :=
            H.parent_compatible coarse fine hcoarseFine original
      exact htransitionOriginal.symm.trans hjtransition
  · intro hj
    rcases
        (P.mem_relationIndices_iff
          representative (chain.index fine.val)
            (chain.index coarse.val) j).mp hj with
      ⟨original, hhistory, hcoarse, hfine⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (P.mem_relationIndices_iff
        i (chain.index fine.val) (chain.index 0) j).mpr
      refine ⟨original, ?_, ?_, hfine⟩
      · have hrepresentativeParent :
            P.parentOf representative = P.parentOf i := by
          funext t
          have hrepresentative :=
            (mem_conditionalParentCell_iff
              U.coarse U.cover P.scale (P.parentOf i)
                representative).mp hrepresentativeHistory t
          simp only [FrostmanConditionalFactorScope.parentOf]
          exact hrepresentative
        simpa [hrepresentativeParent] using hhistory
      · let hzero : (0 : Fin (J + 1)) ≤ coarse :=
          Fin.zero_le coarse
        have hrootOriginal :=
          H.parent_compatible
            (0 : Fin (J + 1)) coarse hzero original
        have hrootRepresentative :=
          H.parent_compatible
            (0 : Fin (J + 1)) coarse hzero representative
        have htransition :
            H.transition (0 : Fin (J + 1)) coarse hzero
                ((U.cover (chain.index coarse.val)).parent original) =
              H.transition (0 : Fin (J + 1)) coarse hzero
                ((U.cover (chain.index coarse.val)).parent representative) :=
          congrArg
            (H.transition (0 : Fin (J + 1)) coarse hzero) hcoarse
        have hroot :
            (U.cover (chain.index 0)).parent original =
              (U.cover (chain.index 0)).parent representative := by
          have hrootFin :
              (U.cover (chain.index (0 : Fin (J + 1)).val)).parent original =
                (U.cover
                  (chain.index (0 : Fin (J + 1)).val)).parent representative :=
            hrootOriginal.symm.trans <|
              htransition.trans hrootRepresentative
          simpa using hrootFin
        exact hroot.trans hrepresentativeRoot
    · calc
        H.transition coarse fine hcoarseFine j
            =
          H.transition coarse fine hcoarseFine
            ((U.cover (chain.index fine.val)).parent original) :=
              congrArg (H.transition coarse fine hcoarseFine)
                hfine.symm
        _ = (U.cover (chain.index coarse.val)).parent original :=
          H.parent_compatible coarse fine hcoarseFine original
        _ = (U.cover (chain.index coarse.val)).parent representative :=
          hcoarse

/-- Descendants at the next level are partitioned by their coherent parent
at the current level. -/
lemma descendantIndices_card_eq_sum_transitionFiber
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (interval : Fin J) :
    ((H.descendantIndices P i interval.succ).card : ENNReal) =
      ∑ parent ∈ H.descendantIndices P i interval.castSucc,
        (((H.descendantIndices P i interval.succ).filter
          (fun child =>
            H.transition interval.castSucc interval.succ
              (Fin.castSucc_le_succ interval) child = parent)).card :
          ENNReal) := by
  classical
  let parentMap :=
    H.transition interval.castSucc interval.succ
      (Fin.castSucc_le_succ interval)
  have hmaps :
      Set.MapsTo parentMap
        (↑(H.descendantIndices P i interval.succ) :
          Set (Fin (U.coarse
            (chain.index interval.succ.val)).card))
        (↑(H.descendantIndices P i interval.castSucc) :
          Set (Fin (U.coarse
            (chain.index interval.castSucc.val)).card)) := by
    intro child hchild
    exact H.transition_mem_descendantIndices
      P i interval.castSucc interval.succ
        (Fin.castSucc_le_succ interval) child hchild
  have hnat :=
    Finset.card_eq_sum_card_fiberwise hmaps
  exact_mod_cast hnat

/-- One coherent edge grows every occupied descendant set by at least the
minimum represented relation cardinality on that edge. -/
lemma relationCardMin_mul_descendantCard_le_next
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (hF : F.Nonempty)
    (i : Fin F.card)
    (interval : Fin J) :
    P.relationCardMin hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval) *
        ((H.descendantIndices P i interval.castSucc).card : ENNReal) ≤
      ((H.descendantIndices P i interval.succ).card : ENNReal) := by
  classical
  let minimum :=
    P.relationCardMin hF
      (chain.fineIndex interval)
      (chain.coarseIndex interval)
  let parentMap :=
    H.transition interval.castSucc interval.succ
      (Fin.castSucc_le_succ interval)
  rw [H.descendantIndices_card_eq_sum_transitionFiber P i interval]
  calc
    minimum *
          ((H.descendantIndices P i interval.castSucc).card : ENNReal)
        =
      ∑ parent ∈ H.descendantIndices P i interval.castSucc,
        minimum := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤
      ∑ parent ∈ H.descendantIndices P i interval.castSucc,
        (((H.descendantIndices P i interval.succ).filter
          (fun child => parentMap child = parent)).card : ENNReal) := by
            apply Finset.sum_le_sum
            intro parent hparent
            rcases
                (P.mem_relationIndices_iff
                  i (chain.index interval.castSucc.val)
                    (chain.index 0) parent).mp hparent with
              ⟨representative, hhistory, hroot, hparentRepresentative⟩
            have hfiber :=
              H.transitionFiber_eq_relationIndices
                P i representative interval.castSucc interval.succ
                  (Fin.castSucc_le_succ interval)
                  hhistory hroot
            rw [hparentRepresentative] at hfiber
            have hminimum :=
              P.relationCardMin_le_represented hF representative
                (chain.fineIndex interval)
                (chain.coarseIndex interval)
            change minimum ≤
              (((H.descendantIndices P i interval.succ).filter
                (fun child => parentMap child = parent)).card : ENNReal)
            rw [show
              (H.descendantIndices P i interval.succ).filter
                  (fun child => parentMap child = parent) =
                P.relationIndices representative
                  (chain.fineIndex interval)
                  (chain.coarseIndex interval) by
              simpa [parentMap,
                GridIndexSubchain.fineIndex,
                GridIndexSubchain.coarseIndex] using hfiber]
            exact hminimum

private lemma relationCardMin_product_range_le_descendantCard
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (hF : F.Nonempty)
    (i : Fin F.card) :
    ∀ (n : ℕ) (hn : n ≤ J),
      (∏ k ∈ Finset.range n,
          P.relationCardMin hF
            (chain.index (k + 1)) (chain.index k)) ≤
        ((H.descendantIndices P i
          ⟨n, Nat.lt_succ_of_le hn⟩).card : ENNReal) := by
  intro n hn
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty]
      have hnonempty :
          (H.descendantIndices P i
            (⟨0, Nat.succ_pos J⟩ : Fin (J + 1))).Nonempty :=
        P.relationIndices_nonempty i (chain.index 0) (chain.index 0)
      exact_mod_cast hnonempty.card_pos
  | succ n inductionHypothesis =>
      have hnJ : n < J := by omega
      have hnLeJ : n ≤ J := Nat.le_of_lt hnJ
      let interval : Fin J := ⟨n, hnJ⟩
      have hprevious :=
        inductionHypothesis hnLeJ
      have hstep :=
        H.relationCardMin_mul_descendantCard_le_next
          P hF i interval
      rw [Finset.prod_range_succ]
      calc
        (∏ k ∈ Finset.range n,
              P.relationCardMin hF
                (chain.index (k + 1)) (chain.index k)) *
            P.relationCardMin hF
              (chain.index (n + 1)) (chain.index n)
            ≤
          ((H.descendantIndices P i
            ⟨n, Nat.lt_succ_of_le hnLeJ⟩).card : ENNReal) *
            P.relationCardMin hF
              (chain.index (n + 1)) (chain.index n) := by
                gcongr
        _ =
          P.relationCardMin hF
              (chain.fineIndex interval)
              (chain.coarseIndex interval) *
            ((H.descendantIndices P i interval.castSucc).card :
              ENNReal) := by
                simp [interval,
                  GridIndexSubchain.fineIndex,
                  GridIndexSubchain.coarseIndex]
                ac_rfl
        _ ≤
          ((H.descendantIndices P i interval.succ).card : ENNReal) :=
            hstep
        _ =
          ((H.descendantIndices P i
            ⟨n + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hnJ)⟩).card :
              ENNReal) := by
                congr 2

/-- Exact nested branching gives the whole-chain minimum-cardinality lower
bound required by the density telescope. -/
theorem relationCardMin_product_le_whole
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (hF : F.Nonempty)
    (hcoarse : chain.index 0 = P.coarse)
    (hfine : chain.index J = P.fine) :
    (∏ interval : Fin J,
        P.relationCardMin hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) ≤
      P.relationCardMin hF P.fine P.coarse := by
  let indices : Finset (Fin F.card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩
  apply Finset.le_inf'
  intro i _hi
  have hrange :=
    H.relationCardMin_product_range_le_descendantCard
      P hF i J le_rfl
  have hfin :
      (∏ interval : Fin J,
          P.relationCardMin hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) =
        ∏ k ∈ Finset.range J,
          P.relationCardMin hF
            (chain.index (k + 1)) (chain.index k) := by
    simpa [GridIndexSubchain.fineIndex,
      GridIndexSubchain.coarseIndex] using
        Fin.prod_univ_eq_prod_range
          (fun k =>
            P.relationCardMin hF
              (chain.index (k + 1)) (chain.index k)) J
  rw [hfin]
  calc
    (∏ k ∈ Finset.range J,
        P.relationCardMin hF
          (chain.index (k + 1)) (chain.index k))
        ≤
      ((H.descendantIndices P i (Fin.last J)).card : ENNReal) := by
        have hlast :
            Fin.last J =
              (⟨J, Nat.lt_succ_self J⟩ : Fin (J + 1)) := by
          apply Fin.ext
          rfl
        rw [hlast]
        exact hrange
    _ =
      P.representedRelationCard i P.fine P.coarse := by
        change
          ((P.relationIndices i (chain.index J) (chain.index 0)).card :
              ENNReal) =
            P.representedRelationCard i P.fine P.coarse
        rw [hfine, hcoarse]
        rfl

/-- Edgewise conditional uniformity plus coherent nested branching gives the
full cardinality telescope. -/
theorem relationCardMax_product_le_uniformity_pow_mul_whole
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (hF : F.Nonempty)
    (hcoarse : chain.index 0 = P.coarse)
    (hfine : chain.index J = P.fine) :
    (∏ interval : Fin J,
        P.relationCardMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) ≤
      U.uniformity ^ (2 * J) *
        P.relationCardMin hF P.fine P.coarse := by
  have hedge :
      ∀ interval : Fin J,
        P.relationCardMax hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval) ≤
          U.uniformity ^ 2 *
            P.relationCardMin hF
              (chain.fineIndex interval)
              (chain.coarseIndex interval) := by
    intro interval
    exact
      P.relationCardMax_le_uniformity_sq_mul_min
        hroom hF
        (chain.fineIndex interval)
        (chain.coarseIndex interval)
  have hminimum :=
    H.relationCardMin_product_le_whole
      P hF hcoarse hfine
  calc
    (∏ interval : Fin J,
        P.relationCardMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval))
        ≤
      ∏ interval : Fin J,
        (U.uniformity ^ 2 *
          P.relationCardMin hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval)) := by
              exact Finset.prod_le_prod
                (fun _ _ => by positivity)
                (fun interval _ => hedge interval)
    _ =
      U.uniformity ^ (2 * J) *
        ∏ interval : Fin J,
          P.relationCardMin hF
            (chain.fineIndex interval)
            (chain.coarseIndex interval) := by
              rw [Finset.prod_mul_distrib]
              simp [pow_mul]
    _ ≤
      U.uniformity ^ (2 * J) *
        P.relationCardMin hF P.fine P.coarse := by
          gcongr

/-- A coherent parent hierarchy supplies the complete reference-density
telescope with loss `uniformity^(2J)`. -/
theorem referenceDensity_product_le_uniformity_pow_mul_whole
    (H : CoherentGridSubchainParentHierarchy U chain)
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A)
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (hF_ball : F.IsInUnitBall)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (hJ : 1 ≤ J)
    (hcoarse : chain.index 0 = P.coarse)
    (hfine : chain.index J = P.fine) :
    (∏ interval : Fin J,
        P.relationReferenceDensityMax hF
          (chain.fineIndex interval)
          (chain.coarseIndex interval)) ≤
      U.uniformity ^ (2 * J) *
        P.relationReferenceDensityMin hF P.fine P.coarse := by
  apply P.referenceDensity_telescope_of_cardinality_telescope
    hA hdelta hF hF_ball hJ chain hcoarse hfine
      (U.uniformity ^ (2 * J))
  exact
    H.relationCardMax_product_le_uniformity_pow_mul_whole
      P hroom hF hcoarse hfine

end CoherentGridSubchainParentHierarchy

end Kakeya.Streamlined
