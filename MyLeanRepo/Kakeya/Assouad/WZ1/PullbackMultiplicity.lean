import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Statements
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Pullback multiplicity and source-fiber combinatorics

These lemmas prove the multiplicity and one-parent support properties required
as fields by the rescaled covered-parent-fiber API.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
If source pieces cover every source carrier and their images lie in the
corresponding target carriers, source point multiplicity is bounded by target
point multiplicity at the image point.
-/
lemma pullback_multiplicity_injective
    {F_fine F_coarse : Kakeya.Streamlined.BodyFamily}
    (sourceShading : Kakeya.Streamlined.Shading F_fine)
    (targetShading : Kakeya.Streamlined.Shading F_coarse)
    (sourceIndex : Fin F_coarse.card → Fin F_fine.card)
    (sourcePiece : Fin F_coarse.card → Set Point3)
    (Φ : Point3 → Point3)
    (h_cover : ∀ i, sourceShading.carrier i ⊆
        ⋃ k : Fin F_coarse.card,
          if sourceIndex k = i then sourcePiece k else ∅)
    (h_image : ∀ k, Φ '' sourcePiece k ⊆ targetShading.carrier k) :
    ∀ p, (sourceShading.pointMultiplicity p : ENNReal) ≤
        (targetShading.pointMultiplicity (Φ p) : ENNReal) := by
  intro p
  classical
  let S :=
    Finset.univ.filter
      (fun i : Fin F_fine.card => p ∈ sourceShading.carrier i)
  let T :=
    Finset.univ.filter
      (fun k : Fin F_coarse.card => Φ p ∈ targetShading.carrier k)
  have h1 : ∀ i ∈ S, ∃ k : Fin F_coarse.card,
      sourceIndex k = i ∧ p ∈ sourcePiece k := by
    intro i hi
    have h_i_in : p ∈ sourceShading.carrier i :=
      (Finset.mem_filter.mp hi).2
    have h2 : p ∈ ⋃ k : Fin F_coarse.card,
        if sourceIndex k = i then sourcePiece k else ∅ :=
      h_cover i h_i_in
    rcases Set.mem_iUnion.mp h2 with ⟨k, hk⟩
    split_ifs at hk with h4
    · exact ⟨k, h4, hk⟩
    · contradiction
  let f : {i : Fin F_fine.card // i ∈ S} → Fin F_coarse.card :=
    fun x => Classical.choose (h1 x.val x.property)
  have hf1 : ∀ x : {i // i ∈ S},
      sourceIndex (f x) = x.val ∧ p ∈ sourcePiece (f x) := by
    intro x
    exact Classical.choose_spec (h1 x.val x.property)
  have h_inj : Function.Injective f := by
    intro x y h
    have h4 : sourceIndex (f x) = x.val := (hf1 x).1
    have h5 : sourceIndex (f y) = y.val := (hf1 y).1
    apply Subtype.ext
    calc
      x.val = sourceIndex (f x) := h4.symm
      _ = sourceIndex (f y) := by rw [h]
      _ = y.val := h5
  have h6 : ∀ x : {i // i ∈ S}, f x ∈ T := by
    intro x
    have h7 : p ∈ sourcePiece (f x) := (hf1 x).2
    have h8 : Φ p ∈ Φ '' sourcePiece (f x) := ⟨p, h7, rfl⟩
    have h9 : Φ p ∈ targetShading.carrier (f x) := h_image (f x) h8
    simpa [T, Finset.mem_filter] using h9
  have h10 : Finset.image f S.attach ⊆ T := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
    exact h6 x
  have h11 : (Finset.image f S.attach).card = S.attach.card :=
    Finset.card_image_of_injective _ h_inj
  have h13 : S.card ≤ T.card := by
    calc
      S.card = S.attach.card := by simp
      _ = (Finset.image f S.attach).card := h11.symm
      _ ≤ T.card := Finset.card_le_card h10
  change (S.card : ENNReal) ≤ (T.card : ENNReal)
  exact_mod_cast h13

/--
If a shading is supported on one parent fiber, fiber point multiplicity equals
global point multiplicity.
-/
lemma fiber_mult_eq_point_mult
    {fine coarse : Kakeya.Streamlined.BodyFamily}
    (P : Kakeya.Streamlined.Factoring fine coarse)
    (Y : Kakeya.Streamlined.Shading fine)
    (parent : Fin coarse.card)
    (h_support : ∀ i p, p ∈ Y.carrier i → P.parent i = parent) :
    ∀ p, P.fiberPointMultiplicity Y parent p = Y.pointMultiplicity p := by
  intro p
  classical
  let S_full :=
    Finset.univ.filter (fun i : Fin fine.card => p ∈ Y.carrier i)
  let S_fiber :=
    (P.fiberIndices parent).filter (fun i => p ∈ Y.carrier i)
  have h1 : S_full ⊆ P.fiberIndices parent := by
    intro i hi
    have h2 : p ∈ Y.carrier i := (Finset.mem_filter.mp hi).2
    have h3 : P.parent i = parent := h_support i p h2
    simpa [Kakeya.Streamlined.Factoring.fiberIndices,
      Finset.mem_filter] using h3
  have h4 : S_fiber = S_full := by
    ext i
    simp only [S_fiber, S_full, Finset.mem_filter]
    constructor
    · intro ⟨_, h6⟩
      exact ⟨Finset.mem_univ i, h6⟩
    · intro ⟨_, h6⟩
      have h7 : i ∈ P.fiberIndices parent :=
        h1 (by simp [S_full, h6])
      exact ⟨h7, h6⟩
  change S_fiber.card = S_full.card
  rw [h4]

/-- The image of the source union lies in the target union. -/
lemma image_union_subset
    {F_fine F_coarse : Kakeya.Streamlined.BodyFamily}
    (sourceShading : Kakeya.Streamlined.Shading F_fine)
    (targetShading : Kakeya.Streamlined.Shading F_coarse)
    (sourceIndex : Fin F_coarse.card → Fin F_fine.card)
    (sourcePiece : Fin F_coarse.card → Set Point3)
    (Φ : Point3 → Point3)
    (h_cover : ∀ i, sourceShading.carrier i ⊆
        ⋃ k : Fin F_coarse.card,
          if sourceIndex k = i then sourcePiece k else ∅)
    (h_image : ∀ k, Φ '' sourcePiece k ⊆ targetShading.carrier k) :
    ∀ p, p ∈ sourceShading.union → Φ p ∈ targetShading.union := by
  intro p hp
  rcases hp with ⟨i, hi⟩
  have h2 : p ∈ ⋃ k : Fin F_coarse.card,
      if sourceIndex k = i then sourcePiece k else ∅ :=
    h_cover i hi
  rcases Set.mem_iUnion.mp h2 with ⟨k, hk⟩
  split_ifs at hk with h4
  · exact ⟨k, h_image k ⟨p, hk, rfl⟩⟩
  · contradiction

/--
Transfer a target constant-multiplicity upper bound to the source through the
pullback multiplicity inequality.
-/
lemma source_point_cap_from_target
    {F_fine F_coarse : Kakeya.Streamlined.BodyFamily}
    (sourceShading : Kakeya.Streamlined.Shading F_fine)
    (targetShading : Kakeya.Streamlined.Shading F_coarse)
    (Φ : Point3 → Point3)
    (m : ℕ) (cap : ENNReal)
    (h_pullback : ∀ p,
      (sourceShading.pointMultiplicity p : ENNReal) ≤
        (targetShading.pointMultiplicity (Φ p) : ENNReal))
    (h_image_union : ∀ p,
      p ∈ sourceShading.union → Φ p ∈ targetShading.union)
    (h_target_const : targetShading.HasConstantMultiplicity m (2 * m))
    (h_target_upper : (2 * m : ENNReal) ≤ cap) :
    ∀ p, (sourceShading.pointMultiplicity p : ENNReal) ≤ cap := by
  intro p
  by_cases h : p ∈ sourceShading.union
  · have hΦ : Φ p ∈ targetShading.union := h_image_union p h
    have h7 : targetShading.pointMultiplicity (Φ p) ≤ 2 * m :=
      (h_target_const (Φ p) hΦ).2
    calc
      (sourceShading.pointMultiplicity p : ENNReal) ≤
          (targetShading.pointMultiplicity (Φ p) : ENNReal) :=
        h_pullback p
      _ ≤ (2 * m : ENNReal) := by exact_mod_cast h7
      _ ≤ cap := h_target_upper
  · have h8 : sourceShading.pointMultiplicity p = 0 := by
      classical
      have h9 :
          Finset.univ.filter
              (fun i : Fin F_fine.card => p ∈ sourceShading.carrier i) =
            ∅ := by
        ext i
        have h10 : p ∉ sourceShading.carrier i := by
          intro h11
          exact h ⟨i, h11⟩
        simp [Finset.mem_filter, h10]
      rw [Kakeya.Streamlined.Shading.pointMultiplicity, h9]
      simp
    rw [h8]
    simp

/-- Restrict a tube shading to one coarse-parent fiber. -/
def restrict_shading_to_parent
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (parent : Fin (U.coarse rho).card)
    (Y : Kakeya.Streamlined.TubeShading F) :
    Kakeya.Streamlined.TubeShading F :=
  { carrier := fun i =>
      if (U.cover rho).parent i = parent then Y.carrier i else ∅
    measurable_carrier := by
      intro i
      split_ifs
      · exact Y.measurable_carrier i
      · exact MeasurableSet.empty
    subset_body := by
      intro i
      split_ifs
      · exact Y.subset_body i
      · exact Set.empty_subset _ }

lemma restrict_shading_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {parent : Fin (U.coarse rho).card}
    {Y : Kakeya.Streamlined.TubeShading F} :
    IsSubshading (restrict_shading_to_parent rho parent Y) Y := by
  intro i
  dsimp only [restrict_shading_to_parent]
  split_ifs
  · exact Set.Subset.rfl
  · exact Set.empty_subset _

lemma restrict_shading_supported
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {parent : Fin (U.coarse rho).card}
    {Y : Kakeya.Streamlined.TubeShading F} :
    ∀ i p, p ∈ (restrict_shading_to_parent rho parent Y).carrier i →
      (U.cover rho).parent i = parent := by
  intro i p hp
  dsimp only [restrict_shading_to_parent] at hp
  split_ifs at hp <;> tauto

/-- The restricted shading mass is the shaded mass in the selected parent. -/
lemma restrict_shading_mass
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {parent : Fin (U.coarse rho).card}
    {Y : Kakeya.Streamlined.TubeShading F} :
    (restrict_shading_to_parent rho parent Y).mass =
      ∑ i ∈ Finset.univ.filter
          (fun i : Fin F.card => (U.cover rho).parent i = parent),
        MeasureTheory.volume (Y.carrier i) := by
  dsimp only [restrict_shading_to_parent, Kakeya.Streamlined.Shading.mass]
  have h1 :
      ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume
          (if (U.cover rho).parent i = parent then
            Y.carrier i else (∅ : Set Point3)) =
        ∑ i : Fin F.toBodyFamily.card,
          if (U.cover rho).parent i = parent then
            MeasureTheory.volume (Y.carrier i) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (U.cover rho).parent i = parent
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      simp
  have h2 :
      ∑ i : Fin F.toBodyFamily.card,
          (if (U.cover rho).parent i = parent then
            MeasureTheory.volume (Y.carrier i) else 0) =
        ∑ i ∈ Finset.univ.filter
            (fun i : Fin F.card => (U.cover rho).parent i = parent),
          MeasureTheory.volume (Y.carrier i) := by
    rw [Finset.sum_filter]
    rfl
  exact h1.trans h2

/-- A positive-radius tube has positive Lebesgue volume. -/
lemma delta_tube_volume_pos
    {delta : ℝ} (hdelta : 0 < delta)
    (T : Kakeya.DeltaTube delta) :
    0 < MeasureTheory.volume T.carrier := by
  have h1 : T.base ∈ Kakeya.unitSegment T.base T.direction := by
    exact ⟨0, by norm_num, by simp⟩
  have h2 : Metric.closedBall T.base delta ⊆ T.carrier :=
    Metric.closedBall_subset_cthickening h1 delta
  have h4 : 0 < MeasureTheory.volume (Metric.closedBall T.base delta) :=
    Metric.measure_closedBall_pos MeasureTheory.volume T.base hdelta
  exact h4.trans_le (MeasureTheory.volume.mono h2)

end Kakeya.Assouad
