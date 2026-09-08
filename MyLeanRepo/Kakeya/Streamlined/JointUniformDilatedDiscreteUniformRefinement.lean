import MyLeanRepo.Kakeya.Streamlined.LocalDilatedDiscreteUniformRefinement

/-!
# Joint-parent uniformity on the independent paper grid

Section 7 recursively restricts one scale fiber and then covers that local
family at another independently selected scale.  The fibers of this local
cover are exactly the nonempty cells cut out by the two parent coordinates.
Uniformity of the two marginal parent maps does not control these joint
cells, so the Section 2 regularization must retain their cardinalities as
additional finite coordinates.

This strengthening does not choose a transition map between covers.  For
each ordered pair of distinguished scales it only compares nonempty sets of
fine tubes having two prescribed parents.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Fine indices with prescribed parents in two independently chosen covers. -/
def jointParentCell
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse :
      ∀ k : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover :
      ∀ k, LocalDilatedTubeCover A C F (coarse k))
    (r s : UniformScaleIndex delta)
    (j : Fin (coarse r).card)
    (k : Fin (coarse s).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    (cover r).parent i = j ∧
      (cover s).parent i = k

@[simp] lemma mem_jointParentCell_iff
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse :
      ∀ k : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover :
      ∀ k, LocalDilatedTubeCover A C F (coarse k))
    (r s : UniformScaleIndex delta)
    (j : Fin (coarse r).card)
    (k : Fin (coarse s).card)
    (i : Fin F.card) :
    i ∈ jointParentCell coarse cover r s j k ↔
      (cover r).parent i = j ∧
        (cover s).parent i = k := by
  simp [jointParentCell]

/--
The strengthened Section 2 output.  It retains the validated independent
coaxial-local covers and additionally balances every nonempty joint-parent
cell for each fixed ordered pair of paper-grid scales.
-/
structure JointUniformLocalDilatedDiscreteUniformTubeStructure
    {delta A C : ℝ} (F : TubeFamily delta)
    (hdelta_le_one : delta ≤ 1)
    extends LocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C) F hdelta_le_one where
  jointUniform :
    ∀ (r s : UniformScaleIndex delta)
      (j : Fin (coarse r).card)
      (k : Fin (coarse s).card)
      (j' : Fin (coarse r).card)
      (k' : Fin (coarse s).card),
      0 < (jointParentCell coarse cover r s j k).card →
      0 < (jointParentCell coarse cover r s j' k').card →
      ((jointParentCell coarse cover r s j k).card : ENNReal) ≤
        assignedUniformity *
          ((jointParentCell coarse cover r s j' k').card : ENNReal)

/--
The Section 7-facing quantitative joint regularization.

For any prescribed recursion depth `N`, one common uniformity constant
controls all marginal cover fibers and all fixed-scale-pair joint cells, and
its `N`-fold loss remains within the requested subpolynomial budget.
-/
def JointUniformLocalDilatedDiscreteUniformPowerBudgetRefinementStatement :
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
                        JointUniformLocalDilatedDiscreteUniformTubeStructure
                          (A := 1000) (C := C) S.family hdelta_le_one,
                      U.uniformity ^ N ≤
                        Kakeya.realRpowENN delta (-epsilon)

end Kakeya.Streamlined
