import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedShading
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopies
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Deterministic helper lemmas for the multiscale random translation theorem

This module collects deterministic facts about translated-copy families,
shading density preservation, nominal mass, and the count bound on J.

## Main results

- `translatedCopies_mass`: total mass of J copies is J times the original mass.
- `tubeSubfamily_mass_le_parent`: subfamily mass ≤ parent mass.
- `translatedShading_density_from_mass_retention`: density preservation under
  mass retention.
- `exists_J_satisfying_count_bound`: existence of J satisfying the count bound.
- `translatedCopies_constant_volume`: all tubes in translated copies have equal volume.
- `translatedCopies_same_copy_distinct`: tubes from the same copy inherit
  essential distinctness from F.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined

namespace Kakeya.Streamlined.RandomTranslation

/-! ### Mass of translated copies -/

/-- A canonical δ-tube for volume comparison. -/
private def canonicalDeltaTube (δ : ℝ) : Kakeya.DeltaTube δ where
  base := 0
  direction := EuclideanSpace.single (0 : Fin 3) 1
  direction_unit := by simp

/-- Every δ-tube has volume equal to `deltaTubeVolume δ`. -/
lemma tube_volume_eq_deltaTubeVolume {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    T.volume = Kakeya.deltaTubeVolume δ := by
  have h1 : T.volume = (canonicalDeltaTube δ).volume :=
    tube_volume_eq T (canonicalDeltaTube δ)
  rw [h1]
  rfl

/--
The mass of the translated-copy family equals J times the original family mass.
-/
lemma translatedCopies_mass
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3} :
    (translatedCopies F J shift).toBodyFamily.mass =
      (J : ENNReal) * F.toBodyFamily.mass := by
  dsimp only [translatedCopies, BodyFamily.mass, TubeFamily.toBodyFamily]
  let e : Equiv (Fin J × Fin F.card) (Fin (J * F.card)) := finProdFinEquiv
  let g : (Fin J × Fin F.card) → ENNReal := fun p =>
    (tubeBody (translateTube (F.tube p.2) (shift p.1))).volume
  have h_eq1 : ∑ (k : Fin (J * F.card)), g (e.symm k) =
      ∑ (p : Fin J × Fin F.card), g p :=
    Equiv.sum_comp e.symm g
  have h_eq2 : ∑ (p : Fin J × Fin F.card), g p =
      ∑ (p : Fin J × Fin F.card), (F.tube p.2).volume := by
    apply Finset.sum_congr rfl
    intro p _
    exact translateTube_volume (F.tube p.2) (shift p.1)
  have h_univ : (Finset.univ : Finset (Fin J × Fin F.card)) =
      (Finset.univ : Finset (Fin J)) ×ˢ (Finset.univ : Finset (Fin F.card)) := by
    ext ⟨a, b⟩
    simp
  have h_prod : ∑ (p : Fin J × Fin F.card), (F.tube p.2).volume =
      ∑ (j : Fin J), ∑ (i : Fin F.card), (F.tube i).volume := by
    rw [h_univ, Finset.sum_product]
    <;> rfl
  have h_const : ∑ (_j : Fin J), ∑ (i : Fin F.card), (F.tube i).volume =
      (J : ENNReal) * ∑ (i : Fin F.card), (F.tube i).volume := by
    rw [Finset.sum_const]
    <;> simp [nsmul_eq_mul]
    <;> ring
  calc
    _ = ∑ (k : Fin (J * F.card)), g (e.symm k) := by rfl
    _ = ∑ (p : Fin J × Fin F.card), g p := h_eq1
    _ = ∑ (p : Fin J × Fin F.card), (F.tube p.2).volume := h_eq2
    _ = ∑ (j : Fin J), ∑ (i : Fin F.card), (F.tube i).volume := h_prod
    _ = (J : ENNReal) * ∑ (i : Fin F.card), (F.tube i).volume := h_const
    _ = (J : ENNReal) * F.toBodyFamily.mass := by rfl

/--
The mass of a tube subfamily is at most the mass of the parent family.
-/
lemma tubeSubfamily_mass_le_parent
    {δ : ℝ} {G : TubeFamily δ} (S : TubeSubfamily G) :
    S.family.toBodyFamily.mass ≤ G.toBodyFamily.mass := by
  let S' := S.toBodySubfamily
  have h : S.family.toBodyFamily.mass =
      ∑ i ∈ Finset.image S.embedding Finset.univ, (G.toBodyFamily.body i).volume :=
    subfamily_mass_eq G.toBodyFamily S'
  rw [h]
  have h2 : Finset.image S.embedding Finset.univ ⊆ (Finset.univ : Finset (Fin G.card)) :=
    Finset.subset_univ _
  exact Finset.sum_le_sum_of_subset_of_nonneg h2 (fun _ _ _ => by positivity)

/-! ### Shading density preservation -/

/--
If the translated subfamily shading retains at least a fraction `c` of the
total shading mass across all copies, and the original shading is `lam`-dense,
then the translated shading is `c * lam`-dense.
-/
lemma translatedShading_density_from_mass_retention
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (S : TubeSubfamily (translatedCopies F J shift))
    (Y : TubeShading F) (c lam : ENNReal)
    (hY_dense : Y.IsLambdaDense lam)
    (h_mass_retention : c * (J : ENNReal) * Y.mass ≤
        (translatedSubfamilyShading S Y).mass) :
    (translatedSubfamilyShading S Y).IsLambdaDense (c * lam) := by
  let Y' := translatedSubfamilyShading S Y
  have hS_mass_le : S.family.toBodyFamily.mass ≤ (J : ENNReal) * F.toBodyFamily.mass := by
    have h1 := tubeSubfamily_mass_le_parent S
    rw [translatedCopies_mass] at h1
    exact h1
  have h6 : (c * lam) * S.family.toBodyFamily.mass ≤
      (c * lam) * ((J : ENNReal) * F.toBodyFamily.mass) :=
    mul_le_mul_left' hS_mass_le (c * lam)
  have h7 : (c * lam) * ((J : ENNReal) * F.toBodyFamily.mass) =
      c * (J : ENNReal) * (lam * F.toBodyFamily.mass) := by ring
  have h8 : c * (J : ENNReal) * (lam * F.toBodyFamily.mass) ≤
      c * (J : ENNReal) * Y.mass :=
    mul_le_mul_left' hY_dense (c * (J : ENNReal))
  have h9 : c * (J : ENNReal) * Y.mass ≤ Y'.mass := h_mass_retention
  exact le_trans (le_trans (le_trans h6 (Eq.le h7)) h8) h9

/-! ### Nominal mass facts -/

/-- The δ-tube volume is positive for δ > 0. -/
lemma deltaTubeVolume_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < Kakeya.deltaTubeVolume δ := by
  have h : ENNReal.ofReal (2 * δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    tube_volume_ge_two_delta_sq δ hδ
  have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
    have h3 : 0 < 2 * δ ^ 2 := by positivity
    exact ENNReal.ofReal_pos.mpr h3
  exact lt_of_lt_of_le h2 h

/-- The δ-tube volume is finite. -/
lemma deltaTubeVolume_ne_top {δ : ℝ} :
    Kakeya.deltaTubeVolume δ ≠ ⊤ := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
  let S : Set Point3 := unitSegment 0 e0
  have h_seg_bdd : Bornology.IsBounded S := by
    have h1 : IsCompact S := by
      apply IsCompact.image
      · exact isCompact_Icc
      · fun_prop
    exact h1.isBounded
  have h_carrier_bdd : Bornology.IsBounded (Metric.cthickening δ S) :=
    h_seg_bdd.cthickening
  exact h_carrier_bdd.measure_lt_top.ne

/-- The nominal mass is positive for a nonempty family and δ > 0. -/
lemma nominalMass_pos {δ : ℝ} {F : TubeFamily δ} (hδ : 0 < δ) (hF : F.Nonempty) :
    0 < F.nominalMass := by
  have h1 : (0 : ENNReal) < F.enncard := by
    dsimp only [TubeFamily.enncard]
    exact_mod_cast hF
  have h2 : 0 < Kakeya.deltaTubeVolume δ := deltaTubeVolume_pos hδ
  dsimp only [TubeFamily.nominalMass]
  exact ENNReal.mul_pos (ne_of_gt h1) (ne_of_gt h2)

/-- The nominal mass is finite. -/
lemma nominalMass_ne_top {δ : ℝ} {F : TubeFamily δ} :
    F.nominalMass ≠ ⊤ := by
  have h1 : F.enncard ≠ ⊤ := by simp [TubeFamily.enncard]
  have h2 : Kakeya.deltaTubeVolume δ ≠ ⊤ := deltaTubeVolume_ne_top
  exact ENNReal.mul_ne_top h1 h2

/-! ### J choice -/

/--
There exists a positive natural number J satisfying the count bound
`J ≤ C * max 1 F.nominalMass⁻¹` whenever `C ≥ 1`.

The choice `J = 1` always works because `max 1 x⁻¹ ≥ 1` for any `x : ENNReal`.
-/
lemma exists_J_satisfying_count_bound
    {δ : ℝ} {F : TubeFamily δ} {C : ENNReal} (hC : 1 ≤ C) :
    ∃ (J : ℕ), 0 < J ∧ (J : ENNReal) ≤ C * max 1 F.nominalMass⁻¹ := by
  have h1 : (1 : ENNReal) ≤ max 1 F.nominalMass⁻¹ := by
    exact le_max_left _ _
  have h2 : (1 : ENNReal) ≤ C * max 1 F.nominalMass⁻¹ := by
    calc
      (1 : ENNReal) ≤ 1 * max 1 F.nominalMass⁻¹ := by simp
      _ ≤ C * max 1 F.nominalMass⁻¹ := by gcongr
  refine ⟨1, by norm_num, ?_⟩
  simpa using h2

/-! ### Equal volume of translated copies -/

/--
Every tube in `translatedCopies F J shift` has the same volume, equal to
the volume of any tube in F (translation preserves volume, and all δ-tubes
have equal volume).
-/
lemma translatedCopies_constant_volume
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hF : F.Nonempty) (i : Fin (J * F.card)) :
    ((translatedCopies F J shift).tube i).volume =
      (F.tube ⟨0, hF⟩).volume := by
  let p : Fin J × Fin F.card := finProdFinEquiv.symm i
  have h1 : (translatedCopies F J shift).tube i =
      translateTube (F.tube p.2) (shift p.1) := by rfl
  rw [h1]
  have h2 : (translateTube (F.tube p.2) (shift p.1)).volume = (F.tube p.2).volume :=
    translateTube_volume (F.tube p.2) (shift p.1)
  rw [h2]
  exact tube_volume_eq (F.tube p.2) (F.tube ⟨0, hF⟩)

/-! ### Essential distinctness within copies -/

/--
Two tubes from the same translated copy are essentially distinct whenever
the original family F is essentially distinct.
-/
lemma translatedCopies_same_copy_distinct
    {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}
    (hF : F.IsEssentiallyDistinct)
    (j : Fin J) (i k : Fin F.card) (hne : i ≠ k) :
    (translateTube (F.tube i) (shift j)).EssentiallyDistinct
      (translateTube (F.tube k) (shift j)) := by
  have h_orig : (F.tube i).EssentiallyDistinct (F.tube k) := hF i k hne
  exact translate_essentiallyDistinct (F.tube i) (F.tube k) (shift j) h_orig

end Kakeya.Streamlined.RandomTranslation

end
