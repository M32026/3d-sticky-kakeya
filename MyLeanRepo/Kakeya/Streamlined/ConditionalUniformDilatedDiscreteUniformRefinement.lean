import MyLeanRepo.Kakeya.Streamlined.LocalDilatedDiscreteUniformRefinement
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentBranching

/-!
# Finite-depth conditional uniformity on the paper grid

The Section 7 stopping time repeatedly conditions the selected fine family on
parent identities at previously chosen scales.  Uniformity of one parent map
or even every pair of parent maps is not closed under this operation: three
binary parent maps may have all pair marginals equal while their triple cells
have arbitrarily different cardinalities.

For a prescribed stopping depth `N`, the correct finite output balances every
nonempty parent cell specified by at most `N + 1` distinguished scales.  This
does not choose transitions between covers.  A cell is defined directly by
the independent ambient parent coordinates of the same fine indices.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Fine indices satisfying a finite list of independent parent constraints. -/
def conditionalParentCell
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse :
      ∀ k : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover :
      ∀ k, LocalDilatedTubeCover A C F (coarse k))
    {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    ∀ t, ((cover (scale t)).parent i).val = parent t

@[simp] lemma mem_conditionalParentCell_iff
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse :
      ∀ k : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover :
      ∀ k, LocalDilatedTubeCover A C F (coarse k))
    {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ)
    (i : Fin F.card) :
    i ∈ conditionalParentCell coarse cover scale parent ↔
      ∀ t, ((cover (scale t)).parent i).val = parent t := by
  simp [conditionalParentCell]

/--
The Section 2 structure closed under at most `depth` recursive splits.

For every fixed nonempty list of at most `depth + 1` scale coordinates, all
nonempty cells of the corresponding joint parent map are comparable by the
same `uniformity`.  Different coordinate lists are not compared.
-/
structure ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
    (depth : ℕ)
    {delta A C : ℝ} (F : TubeFamily delta)
    (hdelta_le_one : delta ≤ 1)
    extends LocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C) F hdelta_le_one where
  delta_pos : 0 < delta
  coverDilation_one : 1 ≤ A
  finest_parent_injective :
    Function.Injective
      (cover (Fin.last (uniformScaleSteps delta))).parent
  finest_parent_carrier_eq :
    ∀ i,
      ((coarse (Fin.last (uniformScaleSteps delta))).tube
          ((cover (Fin.last (uniformScaleSteps delta))).parent i)).carrier =
        (F.tube i).carrier
  coarsest_parent_unique :
    ∀ j k :
      Fin (coarse
        (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).card,
      j = k
  conditionalUniform :
    ∀ {m : ℕ}, 1 ≤ m → m ≤ depth + 1 →
      ∀ (scale : Fin m → UniformScaleIndex delta)
        (parent parent' : Fin m → ℕ),
        0 <
            (conditionalParentCell coarse cover
              scale parent).card →
        0 <
            (conditionalParentCell coarse cover
              scale parent').card →
        ((conditionalParentCell coarse cover
            scale parent).card : ENNReal) ≤
          assignedUniformity *
            ((conditionalParentCell coarse cover
              scale parent').card : ENNReal)
  assigned_to_full :
    uniformity =
      RandomTranslation.fullContainmentBranchingLoss
          A coverDilation_one *
        assignedUniformity

/--
The Section 7-facing finite-depth refinement.

The requested depth is fixed before the small-scale threshold is chosen.
Thus simultaneous regularization may use all coordinate lists of length at
most `N + 1`, while all resulting losses remain subpolynomial in `delta`.
-/
def ConditionalUniformLocalDilatedDiscreteUniformPowerBudgetRefinementStatement :
    Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ N : ℕ, 1 ≤ N →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : TubeFamily delta,
              F.Nonempty →
              F.IsInUnitBall →
              F.IsEssentiallyDistinct →
              ∀ Y : TubeShading F, 0 < Y.mass →
                ∃ S : TubeSubfamily F,
                  S.Nonempty ∧
                  S.RetainsShadedMass Y
                    (Kakeya.realRpowENN delta epsilon) ∧
                  ∃ hdelta_le_one : delta ≤ 1,
                    ∃ U :
                        ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
                          N (A := 1000) (C := C)
                          S.family hdelta_le_one,
                      U.uniformity ^ (2 * N) ≤
                        Kakeya.realRpowENN delta (-epsilon)

end Kakeya.Streamlined
