import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCallerCoarsePrefixSchedule

/-!
# Actual quotient classes in the caller coarse prefix

The caller-prefix schedule labels every quotient class by one caller parent.
Most caller parents need not occur as labels at a coarse coordinate, so using
the whole caller family as the codomain introduces an artificial cardinality
factor.  This module replaces that codomain by the actual image subtype.

The resulting class type has exactly the occupied quotient classes.  The
ambient sizes of any two classes remain comparable by
`prepared.structuralConstant ^ 2`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def WZ2PaperCallerCoarsePrefixClass
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared)) :=
  {label : Fin prepared.callerStrict.coarse.card //
    ∃ parent, schedule.parent coordinate parent = label}

noncomputable instance wz2PaperCallerCoarsePrefixClassFintype
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared)) :
    Fintype
      (WZ2PaperCallerCoarsePrefixClass schedule coordinate) := by
  unfold WZ2PaperCallerCoarsePrefixClass
  infer_instance

noncomputable instance wz2PaperCallerCoarsePrefixClassDecidableEq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared)) :
    DecidableEq
      (WZ2PaperCallerCoarsePrefixClass schedule coordinate) :=
  Classical.decEq _

def WZ2PaperCallerCoarsePrefixScheduleData.classParent
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared))
    (parent : Fin prepared.callerStrict.coarse.card) :
    WZ2PaperCallerCoarsePrefixClass schedule coordinate :=
  ⟨schedule.parent coordinate parent, parent, rfl⟩

theorem
    WZ2PaperCallerCoarsePrefixScheduleData.classParent_nested
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared) :
    ∀ level,
      ∀ hnext :
          level + 1 <
            wz2PaperCallerCoarsePrefixScaleCount prepared,
        ∀ first second,
          schedule.classParent ⟨level + 1, hnext⟩ first =
              schedule.classParent ⟨level + 1, hnext⟩ second →
            schedule.classParent
                ⟨level, Nat.lt_of_succ_lt hnext⟩ first =
              schedule.classParent
                ⟨level, Nat.lt_of_succ_lt hnext⟩ second := by
  intro level hnext first second heq
  apply Subtype.ext
  exact
    schedule.parent_nested level hnext first second <|
      congrArg Subtype.val heq

theorem
    WZ2PaperCallerCoarsePrefixScheduleData.class_ambient_count_uniform
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    (schedule :
      WZ2PaperCallerCoarsePrefixScheduleData prepared)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared))
    (first second :
      WZ2PaperCallerCoarsePrefixClass schedule coordinate) :
    (((Finset.univ :
      Finset (Fin prepared.callerStrict.coarse.card)).filter
      fun parent =>
        schedule.classParent coordinate parent = first).card :
      ENNReal) ≤
      (prepared.structuralConstant *
        prepared.structuralConstant) *
        (((Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          fun parent =>
            schedule.classParent coordinate parent = second).card :
          ENNReal) := by
  have hFirstPos :
      0 <
        ((Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          fun parent =>
            schedule.parent coordinate parent = first.1).card := by
    rcases first.2 with ⟨parent, hparent⟩
    exact
      Finset.card_pos.mpr
        ⟨parent,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hparent⟩⟩
  have hSecondPos :
      0 <
        ((Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          fun parent =>
            schedule.parent coordinate parent = second.1).card := by
    rcases second.2 with ⟨parent, hparent⟩
    exact
      Finset.card_pos.mpr
        ⟨parent,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hparent⟩⟩
  have hFirstFilter :
      (Finset.univ :
        Finset (Fin prepared.callerStrict.coarse.card)).filter
          (fun parent =>
            schedule.classParent coordinate parent = first) =
        (Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          (fun parent =>
            schedule.parent coordinate parent = first.1) := by
    ext parent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext_iff
  have hSecondFilter :
      (Finset.univ :
        Finset (Fin prepared.callerStrict.coarse.card)).filter
          (fun parent =>
            schedule.classParent coordinate parent = second) =
        (Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          (fun parent =>
            schedule.parent coordinate parent = second.1) := by
    ext parent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext_iff
  rw [hFirstFilter, hSecondFilter]
  exact
    schedule.parent_uniform coordinate first.1 second.1
      hFirstPos hSecondPos

end Kakeya.Assouad

end
