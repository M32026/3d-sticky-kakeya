import MyLeanRepo.Kakeya.Streamlined.DilatedDiscreteUniformRefinement
import MyLeanRepo.Kakeya.Streamlined.CloseDistinctTubeCover
import MyLeanRepo.Kakeya.Streamlined.ConditionalUniformDilatedDiscreteUniformRefinement.EndpointCovers
import MyLeanRepo.Kakeya.Streamlined.LocalDilatedTubeCover.Restriction

/-!
# Coaxial-local paper-grid uniform structures

This strengthens the validated finite-grid dilated uniform structure by
retaining scale-local coaxial-line geometry at every distinguished scale.
The cover choices remain independent; no cross-scale transition map is added.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Enlarge only the phase-space error constant of a local dilated cover. -/
def LocalDilatedTubeCover.weakenConstant
    {delta rho A C C' : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : LocalDilatedTubeCover A C fine coarse)
    (hrho : 0 ≤ rho)
    (hCC' : C ≤ C') :
    LocalDilatedTubeCover A C' fine coarse where
  toDilatedTubeCover := cover.toDilatedTubeCover
  transverse_midpoint_close := by
    intro i
    exact (cover.transverse_midpoint_close i).trans <| by
      exact mul_le_mul_of_nonneg_right hCC' hrho
  direction_close_or_reverse := by
    intro i
    rcases cover.direction_close_or_reverse i with h | h
    · exact Or.inl <| h.trans <|
        mul_le_mul_of_nonneg_right hCC' hrho
    · exact Or.inr <| h.trans <|
        mul_le_mul_of_nonneg_right hCC' hrho

@[simp] theorem LocalDilatedTubeCover.weakenConstant_parent
    {delta rho A C C' : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (cover : LocalDilatedTubeCover A C fine coarse)
    (hrho : 0 ≤ rho)
    (hCC' : C ≤ C')
    (index : Fin fine.card) :
    (cover.weakenConstant hrho hCC').parent index =
      cover.parent index :=
  rfl

/--
A finite-grid uniform structure whose one-scale covers preserve transverse
midpoint and orientation-free direction control.
-/
structure LocalDilatedDiscreteUniformTubeStructure
    {delta A C : ℝ} (F : TubeFamily delta)
    (hdelta_le_one : delta ≤ 1) where
  coarse :
    ∀ k : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one k).1
  cover :
    ∀ k, LocalDilatedTubeCover A C F (coarse k)
  coarse_distinct :
    ∀ k, (coarse k).IsEssentiallyDistinct
  assignedUniformity : ENNReal
  one_le_assignedUniformity : 1 ≤ assignedUniformity
  assignedUniformity_ne_top : assignedUniformity ≠ ⊤
  assignedUniform :
    ∀ k,
      (cover k).toDilatedTubeCover.toFactoring.FibersAreCUniform
        assignedUniformity
  uniformity : ENNReal
  assignedUniformity_le_uniformity :
    assignedUniformity ≤ uniformity
  one_le_uniformity : 1 ≤ uniformity
  uniformity_ne_top : uniformity ≠ ⊤
  uniform :
    ∀ k,
      (cover k).toDilatedTubeCover.FullContainmentFibersAreCUniform
        uniformity

/-- Forget local coaxial geometry and retain the validated weak structure. -/
def LocalDilatedDiscreteUniformTubeStructure.toDilated
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : LocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C) F hdelta_le_one) :
    DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one where
  coarse := U.coarse
  cover k := (U.cover k).toDilatedTubeCover
  coarse_distinct := U.coarse_distinct
  assignedUniformity := U.assignedUniformity
  one_le_assignedUniformity := U.one_le_assignedUniformity
  assignedUniformity_ne_top := U.assignedUniformity_ne_top
  assignedUniform := U.assignedUniform
  uniformity := U.uniformity
  assignedUniformity_le_uniformity :=
    U.assignedUniformity_le_uniformity
  one_le_uniformity := U.one_le_uniformity
  uniformity_ne_top := U.uniformity_ne_top
  uniform := U.uniform

/--
Finite-grid existence of independent coaxial-local essentially-distinct
covers.
-/
def FiniteGridLocalDilatedCoverExistenceStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {delta : ℝ}, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ F : TubeFamily delta,
        F.Nonempty →
        F.IsInUnitBall →
        F.IsEssentiallyDistinct →
        ∃ coarse : ∀ k : UniformScaleIndex delta,
            TubeFamily (uniformScale delta hdelta_le_one k).1,
          ∃ cover : ∀ k,
              LocalDilatedTubeCover 1000 C F (coarse k),
            ∀ k, (coarse k).IsEssentiallyDistinct

theorem finite_grid_local_dilated_cover_existence :
    FiniteGridLocalDilatedCoverExistenceStatement := by
  rcases close_distinct_tube_cover_main with ⟨C, hC, hmain⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_le_one F hF_nonempty hF_ball hF_ed
  let H (k : UniformScaleIndex delta) :
      ∃ coarse : TubeFamily (uniformScale delta hdelta_le_one k).1,
        ∃ cover : LocalDilatedTubeCover 1000 C F coarse,
          coarse.IsEssentiallyDistinct := by
    let rho := uniformScale delta hdelta_le_one k
    exact hmain delta rho.1 hdelta rho.2.1 rho.2.2
      F hF_nonempty hF_ball hF_ed
  let coarse (k : UniformScaleIndex delta) := (H k).choose
  let cover (k : UniformScaleIndex delta) := (H k).choose_spec.choose
  exact ⟨coarse, cover, fun k => (H k).choose_spec.choose_spec⟩

/-- A finite local cover system with the canonical singleton unit endpoint. -/
structure FiniteGridLocalDilatedCoverEndpointPackage
    (C : ℝ) {delta : ℝ}
    (F : TubeFamily delta) (hdelta_le_one : delta ≤ 1) where
  coarse :
    ∀ k : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one k).1
  cover :
    ∀ k, LocalDilatedTubeCover 1000 C F (coarse k)
  coarseDistinct :
    ∀ k, (coarse k).IsEssentiallyDistinct
  coarsestParentUnique :
    ∀ j k :
      Fin (coarse
        (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).card,
      j = k
  finestParentInjective :
    Function.Injective
      (cover (Fin.last (uniformScaleSteps delta))).parent
  finestParentCarrierEq :
    ∀ index,
      ((coarse (Fin.last (uniformScaleSteps delta))).tube
        ((cover (Fin.last (uniformScaleSteps delta))).parent index)).carrier =
        (F.tube index).carrier

/--
Independent finite-grid local covers may be chosen with the canonical
singleton unit endpoint.
-/
theorem finite_grid_local_dilated_cover_existence_with_endpoints :
    ∃ C : ℝ, 2 ≤ C ∧
      ∀ {delta : ℝ}, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ F : TubeFamily delta,
        F.Nonempty →
        F.IsInUnitBall →
        F.IsEssentiallyDistinct →
          Nonempty
            (FiniteGridLocalDilatedCoverEndpointPackage
              C F hdelta_le_one) := by
  rcases close_distinct_tube_cover_main with
    ⟨C₀, hC₀, hmain⟩
  let C := max 2 C₀
  have hC : 2 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_le_one F hF hFball hFed
  let unit : UniformScaleIndex delta :=
    ⟨0, Nat.succ_pos _⟩
  let bottom : UniformScaleIndex delta :=
    Fin.last (uniformScaleSteps delta)
  let H (k : UniformScaleIndex delta) :
      ∃ coarse : TubeFamily (uniformScale delta hdelta_le_one k).1,
        ∃ cover : LocalDilatedTubeCover 1000 C F coarse,
          coarse.IsEssentiallyDistinct ∧
            (k = unit →
              ∀ j l : Fin coarse.card, j = l) ∧
            (k = bottom →
              Function.Injective cover.parent ∧
              ∀ index,
                (coarse.tube (cover.parent index)).carrier =
                  (F.tube index).carrier) := by
    by_cases hk : k = unit
    · subst k
      have hscale :
          (uniformScale delta hdelta_le_one unit).1 = 1 := by
        exact uniformScale_zero delta hdelta_le_one
      rw [hscale]
      exact
        ⟨unitScaleTubeFamily,
          unitScaleLocalDilatedTubeCover
            F hF hFball C hC,
          unitScaleTubeFamily_distinct,
          fun _ => unitScaleTubeFamily_unique,
          fun hbottom => by
            have hMpos : 0 < uniformScaleSteps delta := by
              simp [uniformScaleSteps]
            have hzero :
                0 = uniformScaleSteps delta := by
              simpa [unit, bottom] using congrArg Fin.val hbottom
            exact (hMpos.ne' hzero.symm).elim⟩
    · by_cases hkBottom : k = bottom
      · subst k
        have hscale :
            (uniformScale delta hdelta_le_one bottom).1 = delta := by
          exact uniformScale_last delta hdelta_le_one
        rw [hscale]
        let identity :=
          identityLocalDilatedTubeCover
            F C (by linarith) hdelta.le
        exact
          ⟨F, identity, hFed,
            fun h => (hk h).elim,
            fun _ =>
              ⟨identityLocalDilatedTubeCover_injective F,
                identityLocalDilatedTubeCover_carrier_eq F⟩⟩
      · let rho := uniformScale delta hdelta_le_one k
        rcases
            hmain delta rho.1 hdelta rho.2.1 rho.2.2
              F hF hFball hFed with
          ⟨coarse, cover, hcoarse⟩
        exact
          ⟨coarse,
            cover.weakenConstant
              (lt_of_lt_of_le hdelta rho.2.1).le hC₀C,
            hcoarse,
            fun h => (hk h).elim,
            fun h => (hkBottom h).elim⟩
  let coarse (k : UniformScaleIndex delta) := (H k).choose
  let cover (k : UniformScaleIndex delta) :=
    (H k).choose_spec.choose
  have hdistinct :
      ∀ k, (coarse k).IsEssentiallyDistinct :=
    fun k => (H k).choose_spec.choose_spec.1
  have hunique :
      ∀ j k : Fin (coarse unit).card, j = k :=
    (H unit).choose_spec.choose_spec.2.1 rfl
  have hinjective :
      Function.Injective (cover bottom).parent :=
    ((H bottom).choose_spec.choose_spec.2.2 rfl).1
  have hcarrier :
      ∀ index,
        ((coarse bottom).tube ((cover bottom).parent index)).carrier =
          (F.tube index).carrier :=
    ((H bottom).choose_spec.choose_spec.2.2 rfl).2
  exact
    ⟨{
      coarse := coarse
      cover := cover
      coarseDistinct := hdistinct
      coarsestParentUnique := hunique
      finestParentInjective := hinjective
      finestParentCarrierEq := hcarrier
    }⟩

/--
Restrict every independently chosen local cover to an arbitrary fine
subfamily while retaining exact ambient parent identities.
-/
structure RestrictedLocalDilatedCoverSystem
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse : ∀ k : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover : ∀ k, LocalDilatedTubeCover A C F (coarse k))
    (S : TubeSubfamily F) where
  selectedCoarse : ∀ k, TubeSubfamily (coarse k)
  restrictedCover :
    ∀ k, LocalDilatedTubeCover A C S.family (selectedCoarse k).family
  coarse_distinct :
    ∀ k, (selectedCoarse k).family.IsEssentiallyDistinct
  parent_compatible :
    ∀ k i,
      (selectedCoarse k).embedding ((restrictedCover k).parent i) =
        (cover k).parent (S.embedding i)

theorem finite_grid_local_dilated_cover_restriction
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse : ∀ k : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover : ∀ k, LocalDilatedTubeCover A C F (coarse k))
    (hcoarse_distinct : ∀ k, (coarse k).IsEssentiallyDistinct)
    (S : TubeSubfamily F) :
    Nonempty (RestrictedLocalDilatedCoverSystem coarse cover S) := by
  have hmain :
      ∀ k, ∃ R : TubeSubfamily (coarse k),
        R.family.IsEssentiallyDistinct ∧
        ∃ Q : LocalDilatedTubeCover A C S.family R.family,
          ∀ i,
            R.embedding (Q.parent i) =
              (cover k).parent (S.embedding i) := by
    intro k
    exact restrict_local_dilated_tube_cover
      (hcoarse_distinct k) (cover k) S
  choose R hR_distinct Q hQ_compatible using hmain
  exact ⟨{
    selectedCoarse := R
    restrictedCover := Q
    coarse_distinct := hR_distinct
    parent_compatible := hQ_compatible
  }⟩

/--
Legacy quantitative grid refinement with scale-local coaxial geometry retained
at every independently chosen scale.
-/
def LocalDilatedDiscreteUniformRefinementStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ epsilon : ℝ, 0 < epsilon →
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
                  ∃ U : LocalDilatedDiscreteUniformTubeStructure
                      (A := 1000) (C := C) S.family hdelta_le_one,
                    U.uniformity ≤
                      Kakeya.realRpowENN delta (-epsilon)

/--
Internal Section 7 quantitative refinement.

For any prescribed finite stopping-time depth `N`, the common uniformity
loss can be paid at every recursive split while retaining one total
`delta^(-epsilon)` budget.
-/
def LocalDilatedDiscreteUniformPowerBudgetRefinementStatement : Prop :=
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
                    ∃ U : LocalDilatedDiscreteUniformTubeStructure
                        (A := 1000) (C := C) S.family hdelta_le_one,
                      U.uniformity ^ N ≤
                        Kakeya.realRpowENN delta (-epsilon)

end Kakeya.Streamlined
