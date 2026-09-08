import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopiesBasic
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Geometry and cardinality of translated copies

Basic deterministic facts about the explicit indexed family
`translatedCopies F J shift`.
-/

noncomputable section

namespace Kakeya.Streamlined.RandomTranslation

/-- The translated-copy family has exactly `J * F.card` indexed members. -/
@[simp] lemma translatedCopies_card
    {δ : ℝ} (F : TubeFamily δ) (J : ℕ) (shift : Fin J → Point3) :
    (translatedCopies F J shift).card = J * F.card := rfl

/-- ENNReal cardinality of the translated-copy family. -/
lemma translatedCopies_enncard
    {δ : ℝ} (F : TubeFamily δ) (J : ℕ) (shift : Fin J → Point3) :
    (translatedCopies F J shift).enncard =
      (J : ENNReal) * F.enncard := by
  simp [TubeFamily.enncard]

/-- Positive copy and family counts give a nonempty translated-copy family. -/
lemma translatedCopies_nonempty
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hJ : 0 < J) (hF : F.Nonempty) :
    (translatedCopies F J shift).Nonempty := by
  exact Nat.mul_pos hJ hF

/--
Translating a tube contained in the unit ball by a vector of norm at most `9`
places it in the ball of radius `10`.
-/
lemma translateTube_carrier_subset_ball_ten
    {δ : ℝ} {T : Kakeya.DeltaTube δ}
    (hT : T.IsInUnitBall) {v : Point3} (hv : ‖v‖ ≤ 9) :
    (translateTube T v).carrier ⊆ Metric.closedBall (0 : Point3) 10 := by
  rw [translateTube_carrier T v]
  rintro x ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hT hy
  have hnorm : ‖y + v‖ ≤ 10 := by
    calc
      ‖y + v‖ ≤ ‖y‖ + ‖v‖ := norm_add_le _ _
      _ ≤ 1 + 9 := by gcongr
      _ = 10 := by norm_num
  simpa [Metric.mem_closedBall] using hnorm

/--
If all shifts have norm at most `9`, every translated copy of a unit-ball
family lies in the radius-`10` ball.
-/
lemma translatedCopies_in_ball_ten
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hF : F.IsInUnitBall) (hshift : ∀ j, ‖shift j‖ ≤ 9) :
    ∀ i, ((translatedCopies F J shift).tube i).carrier ⊆
      Metric.closedBall (0 : Point3) 10 := by
  intro i
  let p : Fin J × Fin F.card := finProdFinEquiv.symm i
  change (translateTube (F.tube p.2) (shift p.1)).carrier ⊆
    Metric.closedBall (0 : Point3) 10
  exact translateTube_carrier_subset_ball_ten (hF p.2) (hshift p.1)

/-- Any selected translated-copy subfamily remains in the radius-`10` ball. -/
lemma translatedSubfamily_in_ball_ten
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (hF : F.IsInUnitBall) (hshift : ∀ j, ‖shift j‖ ≤ 9) :
    ∀ i, (S.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10 := by
  intro i
  rw [S.tube_eq i]
  exact translatedCopies_in_ball_ten hF hshift (S.embedding i)

end Kakeya.Streamlined.RandomTranslation
