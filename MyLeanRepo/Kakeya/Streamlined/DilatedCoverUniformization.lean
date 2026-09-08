import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# One-scale uniformization of a dilated tube cover

This is the paper-faithful one-scale bridge needed after replacing false
strict coarse-tube containment by universal homothetic dilation.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedTubeCover

/--
Every dilated cover has a canonical, possibly crude, assigned-fiber
uniformity bound.

This theorem derives internal bookkeeping from the parent map; it is not a
field or hypothesis of the paper-facing cover API.
-/
lemma factoringFibersAreCUniform_max_enncard {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse) :
    P.toFactoring.FibersAreCUniform (max 1 fine.enncard) :=
  P.toFactoring.fibersAreCUniform_of_enncard_le
    (le_max_left _ _) (le_max_right _ _)

/-- The factoring fibers partition all fine indices. -/
lemma sum_factoringFiberCount {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse) :
    ∑ j : Fin coarse.card, P.toFactoring.fiberCount j = fine.enncard :=
  P.toFactoring.sum_fiberCount

/-- A finite parent family has one fiber at least as large as every other
fiber. -/
lemma exists_maxFactoringFiber {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty) :
    ∃ j : Fin coarse.card,
      ∀ k : Fin coarse.card,
        P.toFactoring.fiberCount k ≤ P.toFactoring.fiberCount j := by
  classical
  have hcoarse : 0 < coarse.card := by
    let i : Fin fine.card := ⟨0, hfine⟩
    exact lt_of_le_of_lt (Nat.zero_le _) (P.parent i).isLt
  let j₀ : Fin coarse.card := ⟨0, hcoarse⟩
  let fibers : Finset ENNReal :=
    Finset.univ.image P.toFactoring.fiberCount
  have hfibers : fibers.Nonempty :=
    ⟨P.toFactoring.fiberCount j₀,
      Finset.mem_image.mpr ⟨j₀, Finset.mem_univ _, rfl⟩⟩
  let M := fibers.max' hfibers
  have hMmem : M ∈ fibers := fibers.max'_mem hfibers
  rcases Finset.mem_image.mp hMmem with
    ⟨j, _hj, hj⟩
  refine ⟨j, ?_⟩
  intro k
  rw [hj]
  exact fibers.le_max' _ <|
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- The maximum selected fiber controls the total fine cardinality. -/
lemma enncard_le_coarseCard_mul_maxFactoringFiber {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty) :
    ∃ j : Fin coarse.card,
      fine.enncard ≤
        (coarse.card : ENNReal) * P.toFactoring.fiberCount j := by
  rcases P.exists_maxFactoringFiber hfine with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [← P.sum_factoringFiberCount]
  calc
    ∑ k : Fin coarse.card, P.toFactoring.fiberCount k
        ≤ ∑ _k : Fin coarse.card, P.toFactoring.fiberCount j := by
      exact Finset.sum_le_sum fun k _ => hj k
    _ = (coarse.card : ENNReal) * P.toFactoring.fiberCount j := by
      simp [nsmul_eq_mul]

/--
Uniformity compares total fine cardinality with every selected parent fiber.
-/
lemma enncard_le_coarseCard_mul_uniformity_mul_factoringFiberCount
    {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty)
    {C : ENNReal} (huniform : P.toFactoring.FibersAreCUniform C)
    (j : Fin coarse.card) :
    fine.enncard ≤
      (coarse.card : ENNReal) * C * P.toFactoring.fiberCount j := by
  rcases P.enncard_le_coarseCard_mul_maxFactoringFiber hfine with
    ⟨jmax, hmax⟩
  have hcompare :
      P.toFactoring.fiberCount jmax ≤
        C * P.toFactoring.fiberCount j :=
    huniform.2 jmax j
  calc
    fine.enncard
        ≤ (coarse.card : ENNReal) *
            P.toFactoring.fiberCount jmax := hmax
    _ ≤ (coarse.card : ENNReal) *
          (C * P.toFactoring.fiberCount j) := by
      exact mul_le_mul_left' hcompare _
    _ = (coarse.card : ENNReal) * C *
          P.toFactoring.fiberCount j := by
      ring

/-- The cardinality comparison in equal-radius fine mass form. -/
lemma nominalMass_le_coarseCard_mul_uniformity_mul_factoringFiberMass
    {δ ρ A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty)
    {C : ENNReal} (huniform : P.toFactoring.FibersAreCUniform C)
    (j : Fin coarse.card) :
    fine.nominalMass ≤
      (coarse.card : ENNReal) * C *
        (P.toFactoring.fiberCount j * Kakeya.deltaTubeVolume δ) := by
  dsimp only [TubeFamily.nominalMass]
  have hcount :=
    P.enncard_le_coarseCard_mul_uniformity_mul_factoringFiberCount
      hfine huniform j
  calc
    fine.enncard * Kakeya.deltaTubeVolume δ
        ≤ ((coarse.card : ENNReal) * C *
            P.toFactoring.fiberCount j) *
          Kakeya.deltaTubeVolume δ := by
      exact mul_le_mul_right' hcount _
    _ = (coarse.card : ENNReal) * C *
          (P.toFactoring.fiberCount j *
            Kakeya.deltaTubeVolume δ) := by
      ring

end DilatedTubeCover

/--
Internal assigned-cell uniformization for one dilated cover.

This balances the fibers of the auxiliary parent map.  It is not a paper
full-containment uniformity statement.
-/
def AssignedDilatedCoverUniformizationStatement : Prop :=
  ∀ {δ ρ A : ℝ},
    ∀ {fine : TubeFamily δ} {coarse : TubeFamily ρ},
      ∀ P : DilatedTubeCover A fine coarse,
      ∀ Y : TubeShading fine,
        0 < Y.mass →
        ∃ S : TubeSubfamily fine,
          S.Nonempty ∧
          Y.mass ≤
            (Nat.log 2 fine.card + 1 : ENNReal) *
              (S.restrictShading Y).mass ∧
          ∃ C : TubeSubfamily coarse,
            ∃ Q : DilatedTubeCover A S.family C.family,
              Q.toFactoring.FibersAreCUniform 2

/-- Legacy compatibility name for the explicitly assigned statement. -/
abbrev LegacyDilatedCoverUniformizationStatement : Prop :=
  AssignedDilatedCoverUniformizationStatement

end Kakeya.Streamlined
