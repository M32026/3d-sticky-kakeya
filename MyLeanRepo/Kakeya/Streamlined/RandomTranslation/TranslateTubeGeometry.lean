import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeBasic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation geometry of tube families

Translating a tube family by a fixed vector preserves carriers, volumes, and
essential distinctness.  No cover or uniform-structure interface is defined
in this module.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

private lemma translation_isometry (shift : Point3) :
    Isometry (fun point : Point3 => point + shift) := by
  intro first second
  have hsub :
      (first + shift) - (second + shift) = first - second := by
    abel
  simp [edist_dist, dist_eq_norm, hsub]

private lemma translation_surjective (shift : Point3) :
    Function.Surjective (fun point : Point3 => point + shift) := by
  intro point
  refine ⟨point - shift, ?_⟩
  abel

private lemma cthickening_translate
    (delta : ℝ) (set : Set Point3) (shift : Point3) :
    Metric.cthickening delta (translateSet set shift) =
      translateSet (Metric.cthickening delta set) shift := by
  let map : Point3 → Point3 := fun point => point + shift
  have hisometry : Isometry map := translation_isometry shift
  have hsurjective : Function.Surjective map :=
    translation_surjective shift
  ext point
  simp only [Metric.mem_cthickening_iff, translateSet, Set.mem_image]
  constructor
  · intro hpoint
    rcases hsurjective point with ⟨source, rfl⟩
    refine ⟨source, ?_, rfl⟩
    have hinf :
        Metric.infEDist (map source) (map '' set) =
          Metric.infEDist source set :=
      Metric.infEDist_image hisometry
    rw [← hinf]
    exact hpoint
  · rintro ⟨source, hsource, rfl⟩
    have hinf :
        Metric.infEDist (map source) (map '' set) =
          Metric.infEDist source set :=
      Metric.infEDist_image hisometry
    rw [hinf]
    exact Metric.mem_cthickening_iff.mp hsource

/-- Translate every tube in a family by the same vector. -/
def translateTubeFamily
    {delta : ℝ} (family : TubeFamily delta) (shift : Point3) :
    TubeFamily delta where
  card := family.card
  tube index := translateTube (family.tube index) shift

/-- The carrier of a translated tube equals the translated carrier. -/
lemma translateTube_carrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (shift : Point3) :
    (translateTube tube shift).carrier =
      translateSet tube.carrier shift := by
  let map : Point3 → Point3 := fun point => point + shift
  have hsegment :
      unitSegment (tube.base + shift) tube.direction =
        map '' unitSegment tube.base tube.direction := by
    ext point
    simp only [unitSegment, Set.mem_image]
    constructor
    · rintro ⟨parameter, hparameter, rfl⟩
      refine
        ⟨tube.base + parameter • tube.direction,
          ⟨parameter, hparameter, rfl⟩, ?_⟩
      dsimp only [map]
      abel
    · rintro ⟨source, ⟨parameter, hparameter, rfl⟩, hpoint⟩
      refine ⟨parameter, hparameter, ?_⟩
      dsimp only [map] at hpoint
      have heq :
          tube.base + parameter • tube.direction + shift =
            tube.base + shift + parameter • tube.direction := by
        abel
      rw [heq] at hpoint
      exact hpoint
  have hthickening :
      Metric.cthickening delta
          (map '' unitSegment tube.base tube.direction) =
        map '' Metric.cthickening delta
          (unitSegment tube.base tube.direction) :=
    cthickening_translate delta
      (unitSegment tube.base tube.direction) shift
  dsimp only [translateTube, DeltaTube.carrier, translateSet]
  rw [hsegment, hthickening]

/-- A translate of a measurable set is measurable. -/
lemma measurableSet_translateSet
    {set : Set Point3} (hset : MeasurableSet set)
    (shift : Point3) :
    MeasurableSet (translateSet set shift) := by
  have heq :
      translateSet set shift =
        (fun point : Point3 => point - shift) ⁻¹' set := by
    ext point
    simp [translateSet, sub_eq_add_neg]
  rw [heq]
  exact hset.preimage (by fun_prop)

/-- Volume of a translated set equals the original volume. -/
lemma volume_translateSet
    {set : Set Point3} (hset : MeasurableSet set)
    (shift : Point3) :
    volume (translateSet set shift) = volume set := by
  let inverse : Point3 → Point3 := fun point => point - shift
  have heq : translateSet set shift = inverse ⁻¹' set := by
    ext point
    simp [translateSet, inverse, sub_eq_add_neg]
  rw [heq]
  have hpreserving : MeasurePreserving inverse :=
    measurePreserving_add_right volume (-shift)
  exact hpreserving.measure_preimage hset.nullMeasurableSet

/-- Translation preserves tube volume. -/
lemma translateTube_volume
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (shift : Point3) :
    (translateTube tube shift).volume = tube.volume := by
  rw [DeltaTube.volume, translateTube_carrier tube shift,
    DeltaTube.volume]
  exact volume_translateSet Metric.isClosed_cthickening.measurableSet shift

/-- Translation preserves essential distinctness. -/
lemma translate_essentiallyDistinct
    {delta : ℝ} (first second : Kakeya.DeltaTube delta)
    (shift : Point3)
    (hdistinct : first.EssentiallyDistinct second) :
    (translateTube first shift).EssentiallyDistinct
      (translateTube second shift) := by
  have hmeasurable :
      MeasurableSet (first.carrier ∩ second.carrier) :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  have hinjective :
      Function.Injective (fun point : Point3 => point + shift) := by
    intro firstPoint secondPoint heq
    simpa using heq
  have hintersection :
      (translateTube first shift).carrier ∩
          (translateTube second shift).carrier =
        translateSet (first.carrier ∩ second.carrier) shift := by
    rw [translateTube_carrier first shift,
      translateTube_carrier second shift]
    dsimp only [translateSet]
    rw [← Set.image_inter hinjective]
  dsimp only [Kakeya.DeltaTube.EssentiallyDistinct]
  rw [hintersection, volume_translateSet hmeasurable,
    translateTube_volume first shift,
    translateTube_volume second shift]
  exact hdistinct

/-- Translation preserves family essential distinctness. -/
lemma translateFamily_essentiallyDistinct
    {delta : ℝ} {family : TubeFamily delta} {shift : Point3}
    (hdistinct : family.IsEssentiallyDistinct) :
    (translateTubeFamily family shift).IsEssentiallyDistinct := by
  intro first second hne
  exact
    translate_essentiallyDistinct
      (family.tube first) (family.tube second) shift
      (hdistinct first second hne)

end Kakeya.Streamlined.RandomTranslation
