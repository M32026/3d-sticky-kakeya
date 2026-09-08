import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorScopes
import MyLeanRepo.Kakeya.Streamlined.DividingScales.GridArithmetic

/-!
# Finite lists of conditional dividing-scale factors

At recursion level `level`, the paper has `level + 1` relative-scale factors.
Each factor carries an all-branch conditional scope.  Replacing one factor by
its inner and outer scopes increases the list length by one, increases the
historical coordinate depth by at most one, and preserves the product of all
relative scales exactly.

This is the structural stopping-time induction.  Frostman profile preservation
is proved separately from these exact list invariants.
-/

noncomputable section

namespace Kakeya.Streamlined

open FrostmanConditionalFactorScope

/-- Structural state after `level` factor splits. -/
structure FrostmanConditionalFactorState
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one)
    (level : ℕ) where
  factors : List (FrostmanConditionalFactorScope U)
  length_eq : factors.length = level + 1
  coordinateCount_le :
    ∀ P ∈ factors, P.coordinateCount ≤ level
  relativeScale_prod :
    (factors.map FrostmanConditionalFactorScope.relativeScale).prod = delta

namespace FrostmanConditionalFactorState

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Root all-branch factor scope on the full interval from `delta` to `1`. -/
def rootFactor
    (hdelta : 0 < delta) :
    FrostmanConditionalFactorScope U where
  coordinateCount := 0
  coordinateCount_le := Nat.zero_le depth
  scale := fun t => Fin.elim0 t
  fine := Fin.last (uniformScaleSteps delta)
  coarse := ⟨0, Nat.succ_pos _⟩
  fineScale_le_coarseScale := by
    rw [uniformScale_last, uniformScale_zero]
    exact hdelta_le_one

@[simp] lemma rootFactor_relativeScale
    (hdelta : 0 < delta) :
    (rootFactor (U := U) hdelta).relativeScale = delta := by
  dsimp only [rootFactor, FrostmanConditionalFactorScope.relativeScale,
    FrostmanConditionalFactorScope.fineScale,
    FrostmanConditionalFactorScope.coarseScale]
  rw [uniformScale_last, uniformScale_zero]
  simp

/-- Initial one-factor state before any split. -/
def root
    (hdelta : 0 < delta) :
    FrostmanConditionalFactorState U 0 where
  factors := [rootFactor (U := U) hdelta]
  length_eq := by simp
  coordinateCount_le := by
    intro P hP
    simp only [List.mem_singleton] at hP
    subst P
    rfl
  relativeScale_prod := by
    simp [rootFactor_relativeScale]

/--
Replace one displayed factor by its inner and outer children.

The decomposition `before ++ P :: after` makes the selected occurrence
explicit, so duplicate extensionally equal factors cause no ambiguity.
-/
def split
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (hdelta : 0 < delta)
    (hlevel : level < depth)
    (before after : List (FrostmanConditionalFactorScope U))
    (P : FrostmanConditionalFactorScope U)
    (hdecomp : S.factors = before ++ P :: after)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    FrostmanConditionalFactorState U (level + 1) := by
  have hP_level : P.coordinateCount ≤ level := by
    apply S.coordinateCount_le P
    rw [hdecomp]
    simp
  have hroom : P.coordinateCount < depth := by
    omega
  let inner := P.innerChild hroom middle hfine_middle
  let outer := P.outerChild middle hmiddle_coarse
  refine {
    factors := before ++ inner :: outer :: after
    length_eq := ?_
    coordinateCount_le := ?_
    relativeScale_prod := ?_
  }
  · have hlength := S.length_eq
    rw [hdecomp] at hlength
    simp only [List.length_append, List.length_cons] at hlength ⊢
    omega
  · intro Q hQ
    simp only [List.mem_append, List.mem_cons] at hQ
    rcases hQ with hbefore | hQinner | hQouter | hafter
    · have hQold : Q ∈ S.factors := by
        rw [hdecomp]
        simp [hbefore]
      exact (S.coordinateCount_le Q hQold).trans (by omega)
    · subst Q
      change P.coordinateCount + 1 ≤ level + 1
      omega
    · subst Q
      change P.coordinateCount ≤ level + 1
      omega
    · have hQold : Q ∈ S.factors := by
        rw [hdecomp]
        simp [hafter]
      exact (S.coordinateCount_le Q hQold).trans (by omega)
  · have hprod := S.relativeScale_prod
    rw [hdecomp] at hprod
    simp only [List.map_append, List.map_cons, List.prod_append,
      List.prod_cons] at hprod ⊢
    have hchildren :
        inner.relativeScale * outer.relativeScale =
          P.relativeScale := by
      exact
        P.innerChild_relativeScale_mul_outerChild_relativeScale
          hdelta hroom middle hfine_middle hmiddle_coarse
    calc
      (List.map FrostmanConditionalFactorScope.relativeScale before).prod *
            (inner.relativeScale *
              (outer.relativeScale *
                (List.map FrostmanConditionalFactorScope.relativeScale after).prod))
          =
        (List.map FrostmanConditionalFactorScope.relativeScale before).prod *
          ((inner.relativeScale * outer.relativeScale) *
            (List.map FrostmanConditionalFactorScope.relativeScale after).prod) := by
              ring
      _ =
        (List.map FrostmanConditionalFactorScope.relativeScale before).prod *
          (P.relativeScale *
            (List.map FrostmanConditionalFactorScope.relativeScale after).prod) := by
              rw [hchildren]
      _ = delta := hprod

end FrostmanConditionalFactorState

end Kakeya.Streamlined
